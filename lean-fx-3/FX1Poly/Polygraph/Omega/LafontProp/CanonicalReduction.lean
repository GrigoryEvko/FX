import FX1Poly.Polygraph.Omega.LafontProp.DiagramDecisionFires

/-! # Polygraph/Omega/LafontProp/CanonicalReduction — THE DECISION on the Lafont keystone
(LAFONT-PROP r3: canonicalReductionStatement REFUTED zero-axiom + the staged positive bricks)

COMMISSIONED TARGET: `canonicalReductionStatement` — every diagram converts to its own normal
form.  OUTCOME: the statement is FALSE over the shipped congruence, machine-refuted here
(`canonicalReductionStatementIsRefuted`), and `matNatCompletenessStatement` falls with it
(`matNatCompletenessStatementIsRefuted`): the 28-constructor congruence carries interchange and
`id|id` fusion but NO strict-monoidal padding coherence, and a Z2 boundary-parity invariant
(`hasOddAnomalousBoundaryCount`, invariance over all 28 constructors) separates the STATABLE
strictness instance `id0 | delta` from both its normal form and bare `delta` — with EQUAL
matrices.  The refutation section at the end of this file carries the full story, the repair
bill, and the kernel pins.  The staged POSITIVE deliverables (everything the target's true
fragment supports) are shipped alongside:

* THE DERIVED-CONGRUENCE TOOLKIT: identity expansions, whisker-splitting of composites under a
  single-side identity block, the two interchange decompositions of a tensor
  (`tensorSplitsTopThenBottom` / `tensorSplitsBottomThenTop`) — all derived from the structural
  constructors (category laws + middle-four interchange + identity fusion), no new axioms.
* THE PAD SEEDS: the four content-mediated unit-padding eliminations
  `id0 | eta ~ eta`, `eta | id0 ~ eta`, `id0 | epsilon ~ epsilon`, `epsilon | id0 ~ epsilon` —
  each derived by synthesizing the empty identity as `eta ; epsilon` (B4) and cancelling the
  ghost pair through a bialgebra row plus a (co)unit row (B2+C2, B2+C3, B3+M2, B3+M3
  respectively).  These are the ONLY unit-padding eliminations the congruence appears to admit;
  see THE WALL below.
* ETA MOVERS: `etaTensorEtaAsChain` (both nestings), `addFoldsEtaPair` ((eta|eta);mu ~ eta),
  `scaleWireAbsorbsEta` (the scale tower kills a zero input, by structural induction),
  `zeroStackPullsEta` (the newest eta of a zero stack extrudes as a pre-composed generator,
  uniformly in the stack height — an OPEN-INDEX mover), and the wire-under-zeros recursion.
* THE REDUCTION-TRANSFER PRINCIPLE (`reductionTransfersAlongConversion`): if `d ~ e` and `e`
  reduces to ITS normal form, then `d` reduces to ITS OWN normal form — because convertible
  diagrams have EQUAL matrices (r2 soundness) hence SYNTACTICALLY equal normal forms (r2
  extensionality).  The residual therefore only ever needs proving up to convertibility.
* THE FIXED-POINT FAMILY (`canonicalDiagramSatisfiesCanonicalReduction`): every canonical
  diagram `C m n E` — for ALL arities and ALL matrices, an infinite family — satisfies the
  canonical-reduction statement, because normalization is syntactically IDEMPOTENT
  (`canonicalFormIsItsOwnNormalForm`, via r2 soundness + rectangle extensionality).
* FIRST GENERATOR INSTANCES of the target statement: `zeroGen`, `discardGen`, the empty
  identity, padded variants, and derived multi-generator diagrams (the scale tower on eta, the
  folded eta pair, the swap-conjugated eta pair, and the RIGHT-NESTED eta triple — the last one
  crossing a genuine tensor-reassociation via B2 + coassociativity).
* CONDITIONAL STAGE-4 FIRES: the r30 defensive unit/associativity pairs' reductions each
  REDUCE, via the transfer principle, to the single-wire-identity reduction — the exact
  remaining dependency is machine-recorded, no fabricated flip.

## THE ROAD TO THE REFUTATION (the four failed attacks that exposed the conserved quantity)

Every route to the full induction (Lafont peel, NF-composition SEQ/PAR, fan surgery) funnels
through PADDING COHERENCE: convertibility instances of the shapes

  (i)  `id_{k+1} | X  ~  id_k | (id_1 | X)`         (left-pad re-association, open k)
  (ii) `X | id_0  ~  X`, `id_0 | X ~ X`             (unit-pad elimination, X with BOTH
                                                     boundaries nonzero, e.g. X = delta)

The presented congruence carries interchange and `id|id` fusion but NO tensor-associativity or
unit rows, so tensor TREES are rigid except where (a) both siblings are identity blocks
(fusion), or (b) a generator row supplies content-mediated plasticity.  Four genuinely
different attacks failed before the invariant was found:

  1. mfi/fusion sandwiches (expand one factor as a two-stage composite, interchange, refuse) —
     every instance returns to itself; the pad is conserved.
  2. content mediation through B2/B4 + (co)unit rows — kills pads ADJACENT TO eta/epsilon
     (shipped below as the four pad seeds and the eta movers) but for blocks with both
     boundaries nonzero (delta, mu, tau, gadgets, fans) the synthesized ghost pair
     `eta ; epsilon` can only re-fuse to the pad it came from; the ghost cannot cross a
     nonzero-boundary block without the very re-association at issue.
  3. induction on the pad height with fusion at the base — the base case IS (ii), which
     reduces back to (i) one level down (mutual regress, no base).
  4. naturality-row conjugation (Neta/Ndelta + S1-derived inverses) — relates the two nestings
     of the SEEDS but each rewrite re-introduces a padded compound one level deeper.

The conservation suspicion was then made exact: `canonicalReductionStatement` IMPLIES instance
(ii) at X = delta (take d := `id0 | delta`: its normal form is syntactically NF(delta), so the
statement plus transitivity and normal-form idempotence yields `id0 | delta ~ delta`), and the
anomaly-parity invariant refutes exactly that instance — see THE DECISION section.  For the
record, the first blocked configuration on the constructive side was:
`(id_n | eta) ; mergeColumnFan n c ~ id_n` at the rung `id_k | scaleThenSwapGadget (c k)` —
the incoming `id_{k+1} | eta` cannot re-split to meet the rung's `(k | 2)` window without (i).
The positive bricks below are exactly the fragment the invariant permits: every landed
conversion crosses only parity-even windows.

Raw Lean 4 + Init only; zero-axiom; structural recursion only; audit twin with per-decl
`#assert_no_axioms` plus an independent `#print axioms` probe. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FX1Poly.Polygraph.Omega.LafontProp

/-! ## The derived-congruence toolkit -/

/-- Expand a diagram by the identity at its source (the reverse of the structural law). -/
theorem expandIdentityAtSource {sourceArity targetArity : Nat}
    (diagram : WireDiagram sourceArity targetArity) :
    AreConvertibleDiagrams diagram
      (WireDiagram.composeSequential (WireDiagram.identityWires sourceArity) diagram) :=
  AreConvertibleDiagrams.fromSymmetry (AreConvertibleDiagrams.composeIdentitySource diagram)

/-- Expand a diagram by the identity at its target. -/
theorem expandIdentityAtTarget {sourceArity targetArity : Nat}
    (diagram : WireDiagram sourceArity targetArity) :
    AreConvertibleDiagrams diagram
      (WireDiagram.composeSequential diagram (WireDiagram.identityWires targetArity)) :=
  AreConvertibleDiagrams.fromSymmetry (AreConvertibleDiagrams.composeIdentityTarget diagram)

/-- A composite whiskered BELOW by an identity block splits into whiskered stages
(`(first ; second) | id_q  ~  (first | id_q) ; (second | id_q)`) — middle-four interchange
against the split identity. -/
theorem whiskerBottomSplitsCompose {sourceArity middleArity targetArity : Nat}
    (firstStage : WireDiagram sourceArity middleArity)
    (secondStage : WireDiagram middleArity targetArity) (strandCount : Nat) :
    AreConvertibleDiagrams
      (WireDiagram.tensorParallel (WireDiagram.composeSequential firstStage secondStage)
        (WireDiagram.identityWires strandCount))
      (WireDiagram.composeSequential
        (WireDiagram.tensorParallel firstStage (WireDiagram.identityWires strandCount))
        (WireDiagram.tensorParallel secondStage (WireDiagram.identityWires strandCount))) :=
  AreConvertibleDiagrams.fromTransitivity
    (AreConvertibleDiagrams.underTensorParallel
      (AreConvertibleDiagrams.fromReflexivity
        (WireDiagram.composeSequential firstStage secondStage))
      (expandIdentityAtSource (WireDiagram.identityWires strandCount)))
    (AreConvertibleDiagrams.middleFourInterchange firstStage secondStage
      (WireDiagram.identityWires strandCount) (WireDiagram.identityWires strandCount))

/-- A composite whiskered ABOVE by an identity block splits into whiskered stages
(`id_p | (first ; second)  ~  (id_p | first) ; (id_p | second)`). -/
theorem whiskerTopSplitsCompose (strandCount : Nat) {sourceArity middleArity targetArity : Nat}
    (firstStage : WireDiagram sourceArity middleArity)
    (secondStage : WireDiagram middleArity targetArity) :
    AreConvertibleDiagrams
      (WireDiagram.tensorParallel (WireDiagram.identityWires strandCount)
        (WireDiagram.composeSequential firstStage secondStage))
      (WireDiagram.composeSequential
        (WireDiagram.tensorParallel (WireDiagram.identityWires strandCount) firstStage)
        (WireDiagram.tensorParallel (WireDiagram.identityWires strandCount) secondStage)) :=
  AreConvertibleDiagrams.fromTransitivity
    (AreConvertibleDiagrams.underTensorParallel
      (expandIdentityAtSource (WireDiagram.identityWires strandCount))
      (AreConvertibleDiagrams.fromReflexivity
        (WireDiagram.composeSequential firstStage secondStage)))
    (AreConvertibleDiagrams.middleFourInterchange
      (WireDiagram.identityWires strandCount) (WireDiagram.identityWires strandCount)
      firstStage secondStage)

/-- Interchange decomposition, top block first:
`top | bottom  ~  (top | id) ; (id | bottom)`. -/
theorem tensorSplitsTopThenBottom {topSourceArity topTargetArity
    bottomSourceArity bottomTargetArity : Nat}
    (topDiagram : WireDiagram topSourceArity topTargetArity)
    (bottomDiagram : WireDiagram bottomSourceArity bottomTargetArity) :
    AreConvertibleDiagrams (WireDiagram.tensorParallel topDiagram bottomDiagram)
      (WireDiagram.composeSequential
        (WireDiagram.tensorParallel topDiagram (WireDiagram.identityWires bottomSourceArity))
        (WireDiagram.tensorParallel (WireDiagram.identityWires topTargetArity) bottomDiagram)) :=
  AreConvertibleDiagrams.fromTransitivity
    (AreConvertibleDiagrams.underTensorParallel (expandIdentityAtTarget topDiagram)
      (expandIdentityAtSource bottomDiagram))
    (AreConvertibleDiagrams.middleFourInterchange topDiagram
      (WireDiagram.identityWires topTargetArity)
      (WireDiagram.identityWires bottomSourceArity) bottomDiagram)

/-- Interchange decomposition, bottom block first:
`top | bottom  ~  (id | bottom) ; (top | id)`. -/
theorem tensorSplitsBottomThenTop {topSourceArity topTargetArity
    bottomSourceArity bottomTargetArity : Nat}
    (topDiagram : WireDiagram topSourceArity topTargetArity)
    (bottomDiagram : WireDiagram bottomSourceArity bottomTargetArity) :
    AreConvertibleDiagrams (WireDiagram.tensorParallel topDiagram bottomDiagram)
      (WireDiagram.composeSequential
        (WireDiagram.tensorParallel (WireDiagram.identityWires topSourceArity) bottomDiagram)
        (WireDiagram.tensorParallel topDiagram
          (WireDiagram.identityWires bottomTargetArity))) :=
  AreConvertibleDiagrams.fromTransitivity
    (AreConvertibleDiagrams.underTensorParallel (expandIdentityAtSource topDiagram)
      (expandIdentityAtTarget bottomDiagram))
    (AreConvertibleDiagrams.middleFourInterchange
      (WireDiagram.identityWires topSourceArity) topDiagram
      bottomDiagram (WireDiagram.identityWires bottomTargetArity))

/-! ## The four pad seeds — content-mediated unit-padding eliminations

Each synthesizes the empty identity as the ghost pair `eta ; epsilon` (row B4 reversed), pulls
the ghost through one interchange, collapses the resulting eta/epsilon pair with a bialgebra
row (B2 or B3 reversed), and cancels through a (co)unit retraction row.  These derivations are
possible EXACTLY because eta and epsilon have an empty boundary on one side; see THE WALL in
the header for why no analogous elimination is available at delta/mu/tau. -/

/-- `id0 | eta ~ eta` — the empty pad above a zero generator vanishes (B4 + B2 + C2). -/
theorem padTopEtaVanishes :
    AreConvertibleDiagrams
      (WireDiagram.tensorParallel (WireDiagram.identityWires 0) WireDiagram.zeroGen)
      WireDiagram.zeroGen :=
  have expandPad : AreConvertibleDiagrams
      (WireDiagram.tensorParallel (WireDiagram.identityWires 0) WireDiagram.zeroGen)
      (WireDiagram.tensorParallel
        (WireDiagram.composeSequential WireDiagram.zeroGen WireDiagram.discardGen)
        WireDiagram.zeroGen) :=
    AreConvertibleDiagrams.underTensorParallel
      (AreConvertibleDiagrams.fromSymmetry
        AreConvertibleDiagrams.fromDiscardAfterZeroBimonoidRow)
      (AreConvertibleDiagrams.fromReflexivity WireDiagram.zeroGen)
  have expandEta : AreConvertibleDiagrams
      (WireDiagram.tensorParallel
        (WireDiagram.composeSequential WireDiagram.zeroGen WireDiagram.discardGen)
        WireDiagram.zeroGen)
      (WireDiagram.tensorParallel
        (WireDiagram.composeSequential WireDiagram.zeroGen WireDiagram.discardGen)
        (WireDiagram.composeSequential WireDiagram.zeroGen singleWire)) :=
    AreConvertibleDiagrams.underTensorParallel
      (AreConvertibleDiagrams.fromReflexivity
        (WireDiagram.composeSequential WireDiagram.zeroGen WireDiagram.discardGen))
      (expandIdentityAtTarget WireDiagram.zeroGen)
  have interchangeGhost : AreConvertibleDiagrams
      (WireDiagram.tensorParallel
        (WireDiagram.composeSequential WireDiagram.zeroGen WireDiagram.discardGen)
        (WireDiagram.composeSequential WireDiagram.zeroGen singleWire))
      (WireDiagram.composeSequential
        (WireDiagram.tensorParallel WireDiagram.zeroGen WireDiagram.zeroGen)
        (WireDiagram.tensorParallel WireDiagram.discardGen singleWire)) :=
    AreConvertibleDiagrams.middleFourInterchange WireDiagram.zeroGen WireDiagram.discardGen
      WireDiagram.zeroGen singleWire
  have collapseEtaPair : AreConvertibleDiagrams
      (WireDiagram.composeSequential
        (WireDiagram.tensorParallel WireDiagram.zeroGen WireDiagram.zeroGen)
        (WireDiagram.tensorParallel WireDiagram.discardGen singleWire))
      (WireDiagram.composeSequential
        (WireDiagram.composeSequential WireDiagram.zeroGen WireDiagram.copyGen)
        (WireDiagram.tensorParallel WireDiagram.discardGen singleWire)) :=
    AreConvertibleDiagrams.underComposeSequential
      (AreConvertibleDiagrams.fromSymmetry AreConvertibleDiagrams.fromCopyAfterZeroBimonoidRow)
      (AreConvertibleDiagrams.fromReflexivity
        (WireDiagram.tensorParallel WireDiagram.discardGen singleWire))
  have reassociate : AreConvertibleDiagrams
      (WireDiagram.composeSequential
        (WireDiagram.composeSequential WireDiagram.zeroGen WireDiagram.copyGen)
        (WireDiagram.tensorParallel WireDiagram.discardGen singleWire))
      (WireDiagram.composeSequential WireDiagram.zeroGen
        (WireDiagram.composeSequential WireDiagram.copyGen
          (WireDiagram.tensorParallel WireDiagram.discardGen singleWire))) :=
    AreConvertibleDiagrams.composeReassociate WireDiagram.zeroGen WireDiagram.copyGen
      (WireDiagram.tensorParallel WireDiagram.discardGen singleWire)
  have fireCounit : AreConvertibleDiagrams
      (WireDiagram.composeSequential WireDiagram.zeroGen
        (WireDiagram.composeSequential WireDiagram.copyGen
          (WireDiagram.tensorParallel WireDiagram.discardGen singleWire)))
      (WireDiagram.composeSequential WireDiagram.zeroGen (WireDiagram.identityWires 1)) :=
    AreConvertibleDiagrams.underComposeSequential
      (AreConvertibleDiagrams.fromReflexivity WireDiagram.zeroGen)
      AreConvertibleDiagrams.fromCopyLeftCounitRow
  AreConvertibleDiagrams.fromTransitivity expandPad
    (AreConvertibleDiagrams.fromTransitivity expandEta
      (AreConvertibleDiagrams.fromTransitivity interchangeGhost
        (AreConvertibleDiagrams.fromTransitivity collapseEtaPair
          (AreConvertibleDiagrams.fromTransitivity reassociate
            (AreConvertibleDiagrams.fromTransitivity fireCounit
              (AreConvertibleDiagrams.composeIdentityTarget WireDiagram.zeroGen))))))

/-- `eta | id0 ~ eta` — the empty pad below a zero generator vanishes (B4 + B2 + C3). -/
theorem padBottomEtaVanishes :
    AreConvertibleDiagrams
      (WireDiagram.tensorParallel WireDiagram.zeroGen (WireDiagram.identityWires 0))
      WireDiagram.zeroGen :=
  have expandPad : AreConvertibleDiagrams
      (WireDiagram.tensorParallel WireDiagram.zeroGen (WireDiagram.identityWires 0))
      (WireDiagram.tensorParallel WireDiagram.zeroGen
        (WireDiagram.composeSequential WireDiagram.zeroGen WireDiagram.discardGen)) :=
    AreConvertibleDiagrams.underTensorParallel
      (AreConvertibleDiagrams.fromReflexivity WireDiagram.zeroGen)
      (AreConvertibleDiagrams.fromSymmetry
        AreConvertibleDiagrams.fromDiscardAfterZeroBimonoidRow)
  have expandEta : AreConvertibleDiagrams
      (WireDiagram.tensorParallel WireDiagram.zeroGen
        (WireDiagram.composeSequential WireDiagram.zeroGen WireDiagram.discardGen))
      (WireDiagram.tensorParallel
        (WireDiagram.composeSequential WireDiagram.zeroGen singleWire)
        (WireDiagram.composeSequential WireDiagram.zeroGen WireDiagram.discardGen)) :=
    AreConvertibleDiagrams.underTensorParallel (expandIdentityAtTarget WireDiagram.zeroGen)
      (AreConvertibleDiagrams.fromReflexivity
        (WireDiagram.composeSequential WireDiagram.zeroGen WireDiagram.discardGen))
  have interchangeGhost : AreConvertibleDiagrams
      (WireDiagram.tensorParallel
        (WireDiagram.composeSequential WireDiagram.zeroGen singleWire)
        (WireDiagram.composeSequential WireDiagram.zeroGen WireDiagram.discardGen))
      (WireDiagram.composeSequential
        (WireDiagram.tensorParallel WireDiagram.zeroGen WireDiagram.zeroGen)
        (WireDiagram.tensorParallel singleWire WireDiagram.discardGen)) :=
    AreConvertibleDiagrams.middleFourInterchange WireDiagram.zeroGen singleWire
      WireDiagram.zeroGen WireDiagram.discardGen
  have collapseEtaPair : AreConvertibleDiagrams
      (WireDiagram.composeSequential
        (WireDiagram.tensorParallel WireDiagram.zeroGen WireDiagram.zeroGen)
        (WireDiagram.tensorParallel singleWire WireDiagram.discardGen))
      (WireDiagram.composeSequential
        (WireDiagram.composeSequential WireDiagram.zeroGen WireDiagram.copyGen)
        (WireDiagram.tensorParallel singleWire WireDiagram.discardGen)) :=
    AreConvertibleDiagrams.underComposeSequential
      (AreConvertibleDiagrams.fromSymmetry AreConvertibleDiagrams.fromCopyAfterZeroBimonoidRow)
      (AreConvertibleDiagrams.fromReflexivity
        (WireDiagram.tensorParallel singleWire WireDiagram.discardGen))
  have reassociate : AreConvertibleDiagrams
      (WireDiagram.composeSequential
        (WireDiagram.composeSequential WireDiagram.zeroGen WireDiagram.copyGen)
        (WireDiagram.tensorParallel singleWire WireDiagram.discardGen))
      (WireDiagram.composeSequential WireDiagram.zeroGen
        (WireDiagram.composeSequential WireDiagram.copyGen
          (WireDiagram.tensorParallel singleWire WireDiagram.discardGen))) :=
    AreConvertibleDiagrams.composeReassociate WireDiagram.zeroGen WireDiagram.copyGen
      (WireDiagram.tensorParallel singleWire WireDiagram.discardGen)
  have fireCounit : AreConvertibleDiagrams
      (WireDiagram.composeSequential WireDiagram.zeroGen
        (WireDiagram.composeSequential WireDiagram.copyGen
          (WireDiagram.tensorParallel singleWire WireDiagram.discardGen)))
      (WireDiagram.composeSequential WireDiagram.zeroGen (WireDiagram.identityWires 1)) :=
    AreConvertibleDiagrams.underComposeSequential
      (AreConvertibleDiagrams.fromReflexivity WireDiagram.zeroGen)
      AreConvertibleDiagrams.fromCopyRightCounitRow
  AreConvertibleDiagrams.fromTransitivity expandPad
    (AreConvertibleDiagrams.fromTransitivity expandEta
      (AreConvertibleDiagrams.fromTransitivity interchangeGhost
        (AreConvertibleDiagrams.fromTransitivity collapseEtaPair
          (AreConvertibleDiagrams.fromTransitivity reassociate
            (AreConvertibleDiagrams.fromTransitivity fireCounit
              (AreConvertibleDiagrams.composeIdentityTarget WireDiagram.zeroGen))))))

/-- `id0 | epsilon ~ epsilon` — the empty pad above a discard vanishes (B4 + B3 + M2). -/
theorem padTopDiscardVanishes :
    AreConvertibleDiagrams
      (WireDiagram.tensorParallel (WireDiagram.identityWires 0) WireDiagram.discardGen)
      WireDiagram.discardGen :=
  have expandPad : AreConvertibleDiagrams
      (WireDiagram.tensorParallel (WireDiagram.identityWires 0) WireDiagram.discardGen)
      (WireDiagram.tensorParallel
        (WireDiagram.composeSequential WireDiagram.zeroGen WireDiagram.discardGen)
        WireDiagram.discardGen) :=
    AreConvertibleDiagrams.underTensorParallel
      (AreConvertibleDiagrams.fromSymmetry
        AreConvertibleDiagrams.fromDiscardAfterZeroBimonoidRow)
      (AreConvertibleDiagrams.fromReflexivity WireDiagram.discardGen)
  have expandDiscard : AreConvertibleDiagrams
      (WireDiagram.tensorParallel
        (WireDiagram.composeSequential WireDiagram.zeroGen WireDiagram.discardGen)
        WireDiagram.discardGen)
      (WireDiagram.tensorParallel
        (WireDiagram.composeSequential WireDiagram.zeroGen WireDiagram.discardGen)
        (WireDiagram.composeSequential singleWire WireDiagram.discardGen)) :=
    AreConvertibleDiagrams.underTensorParallel
      (AreConvertibleDiagrams.fromReflexivity
        (WireDiagram.composeSequential WireDiagram.zeroGen WireDiagram.discardGen))
      (expandIdentityAtSource WireDiagram.discardGen)
  have interchangeGhost : AreConvertibleDiagrams
      (WireDiagram.tensorParallel
        (WireDiagram.composeSequential WireDiagram.zeroGen WireDiagram.discardGen)
        (WireDiagram.composeSequential singleWire WireDiagram.discardGen))
      (WireDiagram.composeSequential
        (WireDiagram.tensorParallel WireDiagram.zeroGen singleWire)
        (WireDiagram.tensorParallel WireDiagram.discardGen WireDiagram.discardGen)) :=
    AreConvertibleDiagrams.middleFourInterchange WireDiagram.zeroGen WireDiagram.discardGen
      singleWire WireDiagram.discardGen
  have collapseDiscardPair : AreConvertibleDiagrams
      (WireDiagram.composeSequential
        (WireDiagram.tensorParallel WireDiagram.zeroGen singleWire)
        (WireDiagram.tensorParallel WireDiagram.discardGen WireDiagram.discardGen))
      (WireDiagram.composeSequential
        (WireDiagram.tensorParallel WireDiagram.zeroGen singleWire)
        (WireDiagram.composeSequential WireDiagram.addGen WireDiagram.discardGen)) :=
    AreConvertibleDiagrams.underComposeSequential
      (AreConvertibleDiagrams.fromReflexivity
        (WireDiagram.tensorParallel WireDiagram.zeroGen singleWire))
      (AreConvertibleDiagrams.fromSymmetry
        AreConvertibleDiagrams.fromDiscardAfterAddBimonoidRow)
  have reassociate : AreConvertibleDiagrams
      (WireDiagram.composeSequential
        (WireDiagram.tensorParallel WireDiagram.zeroGen singleWire)
        (WireDiagram.composeSequential WireDiagram.addGen WireDiagram.discardGen))
      (WireDiagram.composeSequential
        (WireDiagram.composeSequential
          (WireDiagram.tensorParallel WireDiagram.zeroGen singleWire) WireDiagram.addGen)
        WireDiagram.discardGen) :=
    AreConvertibleDiagrams.fromSymmetry
      (AreConvertibleDiagrams.composeReassociate
        (WireDiagram.tensorParallel WireDiagram.zeroGen singleWire)
        WireDiagram.addGen WireDiagram.discardGen)
  have fireUnit : AreConvertibleDiagrams
      (WireDiagram.composeSequential
        (WireDiagram.composeSequential
          (WireDiagram.tensorParallel WireDiagram.zeroGen singleWire) WireDiagram.addGen)
        WireDiagram.discardGen)
      (WireDiagram.composeSequential (WireDiagram.identityWires 1) WireDiagram.discardGen) :=
    AreConvertibleDiagrams.underComposeSequential
      AreConvertibleDiagrams.fromAddLeftUnitRow
      (AreConvertibleDiagrams.fromReflexivity WireDiagram.discardGen)
  AreConvertibleDiagrams.fromTransitivity expandPad
    (AreConvertibleDiagrams.fromTransitivity expandDiscard
      (AreConvertibleDiagrams.fromTransitivity interchangeGhost
        (AreConvertibleDiagrams.fromTransitivity collapseDiscardPair
          (AreConvertibleDiagrams.fromTransitivity reassociate
            (AreConvertibleDiagrams.fromTransitivity fireUnit
              (AreConvertibleDiagrams.composeIdentitySource WireDiagram.discardGen))))))

/-- `epsilon | id0 ~ epsilon` — the empty pad below a discard vanishes (B4 + B3 + M3). -/
theorem padBottomDiscardVanishes :
    AreConvertibleDiagrams
      (WireDiagram.tensorParallel WireDiagram.discardGen (WireDiagram.identityWires 0))
      WireDiagram.discardGen :=
  have expandPad : AreConvertibleDiagrams
      (WireDiagram.tensorParallel WireDiagram.discardGen (WireDiagram.identityWires 0))
      (WireDiagram.tensorParallel WireDiagram.discardGen
        (WireDiagram.composeSequential WireDiagram.zeroGen WireDiagram.discardGen)) :=
    AreConvertibleDiagrams.underTensorParallel
      (AreConvertibleDiagrams.fromReflexivity WireDiagram.discardGen)
      (AreConvertibleDiagrams.fromSymmetry
        AreConvertibleDiagrams.fromDiscardAfterZeroBimonoidRow)
  have expandDiscard : AreConvertibleDiagrams
      (WireDiagram.tensorParallel WireDiagram.discardGen
        (WireDiagram.composeSequential WireDiagram.zeroGen WireDiagram.discardGen))
      (WireDiagram.tensorParallel
        (WireDiagram.composeSequential singleWire WireDiagram.discardGen)
        (WireDiagram.composeSequential WireDiagram.zeroGen WireDiagram.discardGen)) :=
    AreConvertibleDiagrams.underTensorParallel (expandIdentityAtSource WireDiagram.discardGen)
      (AreConvertibleDiagrams.fromReflexivity
        (WireDiagram.composeSequential WireDiagram.zeroGen WireDiagram.discardGen))
  have interchangeGhost : AreConvertibleDiagrams
      (WireDiagram.tensorParallel
        (WireDiagram.composeSequential singleWire WireDiagram.discardGen)
        (WireDiagram.composeSequential WireDiagram.zeroGen WireDiagram.discardGen))
      (WireDiagram.composeSequential
        (WireDiagram.tensorParallel singleWire WireDiagram.zeroGen)
        (WireDiagram.tensorParallel WireDiagram.discardGen WireDiagram.discardGen)) :=
    AreConvertibleDiagrams.middleFourInterchange singleWire WireDiagram.discardGen
      WireDiagram.zeroGen WireDiagram.discardGen
  have collapseDiscardPair : AreConvertibleDiagrams
      (WireDiagram.composeSequential
        (WireDiagram.tensorParallel singleWire WireDiagram.zeroGen)
        (WireDiagram.tensorParallel WireDiagram.discardGen WireDiagram.discardGen))
      (WireDiagram.composeSequential
        (WireDiagram.tensorParallel singleWire WireDiagram.zeroGen)
        (WireDiagram.composeSequential WireDiagram.addGen WireDiagram.discardGen)) :=
    AreConvertibleDiagrams.underComposeSequential
      (AreConvertibleDiagrams.fromReflexivity
        (WireDiagram.tensorParallel singleWire WireDiagram.zeroGen))
      (AreConvertibleDiagrams.fromSymmetry
        AreConvertibleDiagrams.fromDiscardAfterAddBimonoidRow)
  have reassociate : AreConvertibleDiagrams
      (WireDiagram.composeSequential
        (WireDiagram.tensorParallel singleWire WireDiagram.zeroGen)
        (WireDiagram.composeSequential WireDiagram.addGen WireDiagram.discardGen))
      (WireDiagram.composeSequential
        (WireDiagram.composeSequential
          (WireDiagram.tensorParallel singleWire WireDiagram.zeroGen) WireDiagram.addGen)
        WireDiagram.discardGen) :=
    AreConvertibleDiagrams.fromSymmetry
      (AreConvertibleDiagrams.composeReassociate
        (WireDiagram.tensorParallel singleWire WireDiagram.zeroGen)
        WireDiagram.addGen WireDiagram.discardGen)
  have fireUnit : AreConvertibleDiagrams
      (WireDiagram.composeSequential
        (WireDiagram.composeSequential
          (WireDiagram.tensorParallel singleWire WireDiagram.zeroGen) WireDiagram.addGen)
        WireDiagram.discardGen)
      (WireDiagram.composeSequential (WireDiagram.identityWires 1) WireDiagram.discardGen) :=
    AreConvertibleDiagrams.underComposeSequential
      AreConvertibleDiagrams.fromAddRightUnitRow
      (AreConvertibleDiagrams.fromReflexivity WireDiagram.discardGen)
  AreConvertibleDiagrams.fromTransitivity expandPad
    (AreConvertibleDiagrams.fromTransitivity expandDiscard
      (AreConvertibleDiagrams.fromTransitivity interchangeGhost
        (AreConvertibleDiagrams.fromTransitivity collapseDiscardPair
          (AreConvertibleDiagrams.fromTransitivity reassociate
            (AreConvertibleDiagrams.fromTransitivity fireUnit
              (AreConvertibleDiagrams.composeIdentitySource WireDiagram.discardGen))))))

/-! ## Eta movers -/

/-- `eta | eta ~ eta ; (eta | id1)` — the TOP eta of a pair extrudes as a pre-composition. -/
theorem etaTensorEtaAsChain :
    AreConvertibleDiagrams
      (WireDiagram.tensorParallel WireDiagram.zeroGen WireDiagram.zeroGen)
      (WireDiagram.composeSequential WireDiagram.zeroGen
        (WireDiagram.tensorParallel WireDiagram.zeroGen singleWire)) :=
  have expandBoth : AreConvertibleDiagrams
      (WireDiagram.tensorParallel WireDiagram.zeroGen WireDiagram.zeroGen)
      (WireDiagram.tensorParallel
        (WireDiagram.composeSequential (WireDiagram.identityWires 0) WireDiagram.zeroGen)
        (WireDiagram.composeSequential WireDiagram.zeroGen singleWire)) :=
    AreConvertibleDiagrams.underTensorParallel (expandIdentityAtSource WireDiagram.zeroGen)
      (expandIdentityAtTarget WireDiagram.zeroGen)
  have interchangeGhost : AreConvertibleDiagrams
      (WireDiagram.tensorParallel
        (WireDiagram.composeSequential (WireDiagram.identityWires 0) WireDiagram.zeroGen)
        (WireDiagram.composeSequential WireDiagram.zeroGen singleWire))
      (WireDiagram.composeSequential
        (WireDiagram.tensorParallel (WireDiagram.identityWires 0) WireDiagram.zeroGen)
        (WireDiagram.tensorParallel WireDiagram.zeroGen singleWire)) :=
    AreConvertibleDiagrams.middleFourInterchange (WireDiagram.identityWires 0)
      WireDiagram.zeroGen WireDiagram.zeroGen singleWire
  have killPad : AreConvertibleDiagrams
      (WireDiagram.composeSequential
        (WireDiagram.tensorParallel (WireDiagram.identityWires 0) WireDiagram.zeroGen)
        (WireDiagram.tensorParallel WireDiagram.zeroGen singleWire))
      (WireDiagram.composeSequential WireDiagram.zeroGen
        (WireDiagram.tensorParallel WireDiagram.zeroGen singleWire)) :=
    AreConvertibleDiagrams.underComposeSequential padTopEtaVanishes
      (AreConvertibleDiagrams.fromReflexivity
        (WireDiagram.tensorParallel WireDiagram.zeroGen singleWire))
  AreConvertibleDiagrams.fromTransitivity expandBoth
    (AreConvertibleDiagrams.fromTransitivity interchangeGhost killPad)

/-- `eta | eta ~ eta ; (id1 | eta)` — the BOTTOM eta of a pair extrudes as a pre-composition. -/
theorem etaTensorEtaAsChainMirror :
    AreConvertibleDiagrams
      (WireDiagram.tensorParallel WireDiagram.zeroGen WireDiagram.zeroGen)
      (WireDiagram.composeSequential WireDiagram.zeroGen
        (WireDiagram.tensorParallel singleWire WireDiagram.zeroGen)) :=
  have expandBoth : AreConvertibleDiagrams
      (WireDiagram.tensorParallel WireDiagram.zeroGen WireDiagram.zeroGen)
      (WireDiagram.tensorParallel
        (WireDiagram.composeSequential WireDiagram.zeroGen singleWire)
        (WireDiagram.composeSequential (WireDiagram.identityWires 0) WireDiagram.zeroGen)) :=
    AreConvertibleDiagrams.underTensorParallel (expandIdentityAtTarget WireDiagram.zeroGen)
      (expandIdentityAtSource WireDiagram.zeroGen)
  have interchangeGhost : AreConvertibleDiagrams
      (WireDiagram.tensorParallel
        (WireDiagram.composeSequential WireDiagram.zeroGen singleWire)
        (WireDiagram.composeSequential (WireDiagram.identityWires 0) WireDiagram.zeroGen))
      (WireDiagram.composeSequential
        (WireDiagram.tensorParallel WireDiagram.zeroGen (WireDiagram.identityWires 0))
        (WireDiagram.tensorParallel singleWire WireDiagram.zeroGen)) :=
    AreConvertibleDiagrams.middleFourInterchange WireDiagram.zeroGen singleWire
      (WireDiagram.identityWires 0) WireDiagram.zeroGen
  have killPad : AreConvertibleDiagrams
      (WireDiagram.composeSequential
        (WireDiagram.tensorParallel WireDiagram.zeroGen (WireDiagram.identityWires 0))
        (WireDiagram.tensorParallel singleWire WireDiagram.zeroGen))
      (WireDiagram.composeSequential WireDiagram.zeroGen
        (WireDiagram.tensorParallel singleWire WireDiagram.zeroGen)) :=
    AreConvertibleDiagrams.underComposeSequential padBottomEtaVanishes
      (AreConvertibleDiagrams.fromReflexivity
        (WireDiagram.tensorParallel singleWire WireDiagram.zeroGen))
  AreConvertibleDiagrams.fromTransitivity expandBoth
    (AreConvertibleDiagrams.fromTransitivity interchangeGhost killPad)

/-- `(eta | eta) ; mu ~ eta` — the add generator folds a pair of zeros to one zero
(extrusion + the left-unit retraction M2). -/
theorem addFoldsEtaPair :
    AreConvertibleDiagrams
      (WireDiagram.composeSequential
        (WireDiagram.tensorParallel WireDiagram.zeroGen WireDiagram.zeroGen)
        WireDiagram.addGen)
      WireDiagram.zeroGen :=
  have extrude : AreConvertibleDiagrams
      (WireDiagram.composeSequential
        (WireDiagram.tensorParallel WireDiagram.zeroGen WireDiagram.zeroGen)
        WireDiagram.addGen)
      (WireDiagram.composeSequential
        (WireDiagram.composeSequential WireDiagram.zeroGen
          (WireDiagram.tensorParallel WireDiagram.zeroGen singleWire))
        WireDiagram.addGen) :=
    AreConvertibleDiagrams.underComposeSequential etaTensorEtaAsChain
      (AreConvertibleDiagrams.fromReflexivity WireDiagram.addGen)
  have reassociate : AreConvertibleDiagrams
      (WireDiagram.composeSequential
        (WireDiagram.composeSequential WireDiagram.zeroGen
          (WireDiagram.tensorParallel WireDiagram.zeroGen singleWire))
        WireDiagram.addGen)
      (WireDiagram.composeSequential WireDiagram.zeroGen
        (WireDiagram.composeSequential
          (WireDiagram.tensorParallel WireDiagram.zeroGen singleWire) WireDiagram.addGen)) :=
    AreConvertibleDiagrams.composeReassociate WireDiagram.zeroGen
      (WireDiagram.tensorParallel WireDiagram.zeroGen singleWire) WireDiagram.addGen
  have fireUnit : AreConvertibleDiagrams
      (WireDiagram.composeSequential WireDiagram.zeroGen
        (WireDiagram.composeSequential
          (WireDiagram.tensorParallel WireDiagram.zeroGen singleWire) WireDiagram.addGen))
      (WireDiagram.composeSequential WireDiagram.zeroGen (WireDiagram.identityWires 1)) :=
    AreConvertibleDiagrams.underComposeSequential
      (AreConvertibleDiagrams.fromReflexivity WireDiagram.zeroGen)
      AreConvertibleDiagrams.fromAddLeftUnitRow
  AreConvertibleDiagrams.fromTransitivity extrude
    (AreConvertibleDiagrams.fromTransitivity reassociate
      (AreConvertibleDiagrams.fromTransitivity fireUnit
        (AreConvertibleDiagrams.composeIdentityTarget WireDiagram.zeroGen)))

/-- `eta ; scaleWire s ~ eta` — the copy-add scale tower absorbs a zero input, for EVERY scale
factor (structural induction; B2 to split the zero, the inductive hypothesis on the scaled
branch, then the eta-pair fold). -/
theorem scaleWireAbsorbsEta : (scaleFactor : Nat) ->
    AreConvertibleDiagrams
      (WireDiagram.composeSequential WireDiagram.zeroGen (scaleWire scaleFactor))
      WireDiagram.zeroGen
  | 0 =>
      have regroup : AreConvertibleDiagrams
          (WireDiagram.composeSequential WireDiagram.zeroGen
            (WireDiagram.composeSequential WireDiagram.discardGen WireDiagram.zeroGen))
          (WireDiagram.composeSequential
            (WireDiagram.composeSequential WireDiagram.zeroGen WireDiagram.discardGen)
            WireDiagram.zeroGen) :=
        AreConvertibleDiagrams.fromSymmetry
          (AreConvertibleDiagrams.composeReassociate WireDiagram.zeroGen WireDiagram.discardGen
            WireDiagram.zeroGen)
      have fireGhost : AreConvertibleDiagrams
          (WireDiagram.composeSequential
            (WireDiagram.composeSequential WireDiagram.zeroGen WireDiagram.discardGen)
            WireDiagram.zeroGen)
          (WireDiagram.composeSequential (WireDiagram.identityWires 0) WireDiagram.zeroGen) :=
        AreConvertibleDiagrams.underComposeSequential
          AreConvertibleDiagrams.fromDiscardAfterZeroBimonoidRow
          (AreConvertibleDiagrams.fromReflexivity WireDiagram.zeroGen)
      AreConvertibleDiagrams.fromTransitivity regroup
        (AreConvertibleDiagrams.fromTransitivity fireGhost
          (AreConvertibleDiagrams.composeIdentitySource WireDiagram.zeroGen))
  | scaleFactorPred + 1 =>
      have regroupCopy : AreConvertibleDiagrams
          (WireDiagram.composeSequential WireDiagram.zeroGen (scaleWire (scaleFactorPred + 1)))
          (WireDiagram.composeSequential
            (WireDiagram.composeSequential WireDiagram.zeroGen WireDiagram.copyGen)
            (WireDiagram.composeSequential
              (WireDiagram.tensorParallel (scaleWire scaleFactorPred) singleWire)
              WireDiagram.addGen)) :=
        AreConvertibleDiagrams.fromSymmetry
          (AreConvertibleDiagrams.composeReassociate WireDiagram.zeroGen WireDiagram.copyGen
            (WireDiagram.composeSequential
              (WireDiagram.tensorParallel (scaleWire scaleFactorPred) singleWire)
              WireDiagram.addGen))
      have splitZero : AreConvertibleDiagrams
          (WireDiagram.composeSequential
            (WireDiagram.composeSequential WireDiagram.zeroGen WireDiagram.copyGen)
            (WireDiagram.composeSequential
              (WireDiagram.tensorParallel (scaleWire scaleFactorPred) singleWire)
              WireDiagram.addGen))
          (WireDiagram.composeSequential
            (WireDiagram.tensorParallel WireDiagram.zeroGen WireDiagram.zeroGen)
            (WireDiagram.composeSequential
              (WireDiagram.tensorParallel (scaleWire scaleFactorPred) singleWire)
              WireDiagram.addGen)) :=
        AreConvertibleDiagrams.underComposeSequential
          AreConvertibleDiagrams.fromCopyAfterZeroBimonoidRow
          (AreConvertibleDiagrams.fromReflexivity
            (WireDiagram.composeSequential
              (WireDiagram.tensorParallel (scaleWire scaleFactorPred) singleWire)
              WireDiagram.addGen))
      have regroupScale : AreConvertibleDiagrams
          (WireDiagram.composeSequential
            (WireDiagram.tensorParallel WireDiagram.zeroGen WireDiagram.zeroGen)
            (WireDiagram.composeSequential
              (WireDiagram.tensorParallel (scaleWire scaleFactorPred) singleWire)
              WireDiagram.addGen))
          (WireDiagram.composeSequential
            (WireDiagram.composeSequential
              (WireDiagram.tensorParallel WireDiagram.zeroGen WireDiagram.zeroGen)
              (WireDiagram.tensorParallel (scaleWire scaleFactorPred) singleWire))
            WireDiagram.addGen) :=
        AreConvertibleDiagrams.fromSymmetry
          (AreConvertibleDiagrams.composeReassociate
            (WireDiagram.tensorParallel WireDiagram.zeroGen WireDiagram.zeroGen)
            (WireDiagram.tensorParallel (scaleWire scaleFactorPred) singleWire)
            WireDiagram.addGen)
      have absorbScaledBranch : AreConvertibleDiagrams
          (WireDiagram.composeSequential
            (WireDiagram.tensorParallel WireDiagram.zeroGen WireDiagram.zeroGen)
            (WireDiagram.tensorParallel (scaleWire scaleFactorPred) singleWire))
          (WireDiagram.tensorParallel WireDiagram.zeroGen WireDiagram.zeroGen) :=
        AreConvertibleDiagrams.fromTransitivity
          (AreConvertibleDiagrams.fromSymmetry
            (AreConvertibleDiagrams.middleFourInterchange WireDiagram.zeroGen
              (scaleWire scaleFactorPred) WireDiagram.zeroGen singleWire))
          (AreConvertibleDiagrams.underTensorParallel
            (scaleWireAbsorbsEta scaleFactorPred)
            (AreConvertibleDiagrams.composeIdentityTarget WireDiagram.zeroGen))
      have collapseStages : AreConvertibleDiagrams
          (WireDiagram.composeSequential
            (WireDiagram.composeSequential
              (WireDiagram.tensorParallel WireDiagram.zeroGen WireDiagram.zeroGen)
              (WireDiagram.tensorParallel (scaleWire scaleFactorPred) singleWire))
            WireDiagram.addGen)
          (WireDiagram.composeSequential
            (WireDiagram.tensorParallel WireDiagram.zeroGen WireDiagram.zeroGen)
            WireDiagram.addGen) :=
        AreConvertibleDiagrams.underComposeSequential absorbScaledBranch
          (AreConvertibleDiagrams.fromReflexivity WireDiagram.addGen)
      AreConvertibleDiagrams.fromTransitivity regroupCopy
        (AreConvertibleDiagrams.fromTransitivity splitZero
          (AreConvertibleDiagrams.fromTransitivity regroupScale
            (AreConvertibleDiagrams.fromTransitivity collapseStages addFoldsEtaPair)))

/-- `Z n | eta ~ eta ; (Z n | id1)` — the newest eta of a zero stack extrudes as a
pre-composed generator, UNIFORMLY in the stack height (an open-index mover: the id0-pad of the
stack aligns with the interchange window, so no re-association is needed). -/
theorem zeroStackPullsEta (stackHeight : Nat) :
    AreConvertibleDiagrams
      (WireDiagram.tensorParallel (zeroVectorDiagram stackHeight) WireDiagram.zeroGen)
      (WireDiagram.composeSequential WireDiagram.zeroGen
        (WireDiagram.tensorParallel (zeroVectorDiagram stackHeight) singleWire)) :=
  have expandBoth : AreConvertibleDiagrams
      (WireDiagram.tensorParallel (zeroVectorDiagram stackHeight) WireDiagram.zeroGen)
      (WireDiagram.tensorParallel
        (WireDiagram.composeSequential (WireDiagram.identityWires 0)
          (zeroVectorDiagram stackHeight))
        (WireDiagram.composeSequential WireDiagram.zeroGen singleWire)) :=
    AreConvertibleDiagrams.underTensorParallel
      (expandIdentityAtSource (zeroVectorDiagram stackHeight))
      (expandIdentityAtTarget WireDiagram.zeroGen)
  have interchangeGhost : AreConvertibleDiagrams
      (WireDiagram.tensorParallel
        (WireDiagram.composeSequential (WireDiagram.identityWires 0)
          (zeroVectorDiagram stackHeight))
        (WireDiagram.composeSequential WireDiagram.zeroGen singleWire))
      (WireDiagram.composeSequential
        (WireDiagram.tensorParallel (WireDiagram.identityWires 0) WireDiagram.zeroGen)
        (WireDiagram.tensorParallel (zeroVectorDiagram stackHeight) singleWire)) :=
    AreConvertibleDiagrams.middleFourInterchange (WireDiagram.identityWires 0)
      (zeroVectorDiagram stackHeight) WireDiagram.zeroGen singleWire
  have killPad : AreConvertibleDiagrams
      (WireDiagram.composeSequential
        (WireDiagram.tensorParallel (WireDiagram.identityWires 0) WireDiagram.zeroGen)
        (WireDiagram.tensorParallel (zeroVectorDiagram stackHeight) singleWire))
      (WireDiagram.composeSequential WireDiagram.zeroGen
        (WireDiagram.tensorParallel (zeroVectorDiagram stackHeight) singleWire)) :=
    AreConvertibleDiagrams.underComposeSequential padTopEtaVanishes
      (AreConvertibleDiagrams.fromReflexivity
        (WireDiagram.tensorParallel (zeroVectorDiagram stackHeight) singleWire))
  AreConvertibleDiagrams.fromTransitivity expandBoth
    (AreConvertibleDiagrams.fromTransitivity interchangeGhost killPad)

/-- The wire-under-zeros recursion: `Z (k+1) | id1 ~ (eta | id1) ; ((Z k | id1) | id1)` — one
zero of the stack extrudes past the tracked bottom wire (open-index; feeds the next round's
fan-surgery inductions). -/
theorem wireUnderZeroStackRecursion (stackHeight : Nat) :
    AreConvertibleDiagrams
      (WireDiagram.tensorParallel (zeroVectorDiagram (stackHeight + 1)) singleWire)
      (WireDiagram.composeSequential
        (WireDiagram.tensorParallel WireDiagram.zeroGen singleWire)
        (WireDiagram.tensorParallel
          (WireDiagram.tensorParallel (zeroVectorDiagram stackHeight) singleWire)
          singleWire)) :=
  AreConvertibleDiagrams.fromTransitivity
    (AreConvertibleDiagrams.underTensorParallel (zeroStackPullsEta stackHeight)
      (AreConvertibleDiagrams.fromReflexivity singleWire))
    (whiskerBottomSplitsCompose WireDiagram.zeroGen
      (WireDiagram.tensorParallel (zeroVectorDiagram stackHeight) singleWire) 1)

/-- THE FRONTIER LEMMA: a zero generator entering a one-column canonical form reaches the
column fan — `eta ; C 1 n E ~ (Z n | eta) ; F n (E-column)`.  This is the exact pre-wall
segment of the eta-absorption `eta ; C 1 n E ~ Z n`: the remaining step — the fan absorbing
the extruded eta, `(Z n | eta) ; F n c ~ Z n` — is the first blocked configuration of THE WALL
(the incoming `((n+1) | 1)`-split stack cannot meet the fan rung's `(k | 2)` window without
padding coherence). -/
theorem zeroGenEntersCanonicalColumn (targetArity : Nat) (entries : MatrixEntries) :
    AreConvertibleDiagrams
      (WireDiagram.composeSequential WireDiagram.zeroGen
        (canonicalDiagramOfEntries 1 targetArity entries))
      (WireDiagram.composeSequential
        (WireDiagram.tensorParallel (zeroVectorDiagram targetArity) WireDiagram.zeroGen)
        (mergeColumnFan targetArity (fun mergeRow => entries mergeRow 0))) :=
  AreConvertibleDiagrams.fromTransitivity
    (AreConvertibleDiagrams.fromSymmetry
      (AreConvertibleDiagrams.composeReassociate WireDiagram.zeroGen
        (WireDiagram.tensorParallel (zeroVectorDiagram targetArity) singleWire)
        (mergeColumnFan targetArity (fun mergeRow => entries mergeRow 0))))
    (AreConvertibleDiagrams.underComposeSequential
      (AreConvertibleDiagrams.fromSymmetry (zeroStackPullsEta targetArity))
      (AreConvertibleDiagrams.fromReflexivity
        (mergeColumnFan targetArity (fun mergeRow => entries mergeRow 0))))

/-! ## The reduction-transfer principle and the canonical fixed-point family -/

/-- THE REDUCTION-TRANSFER PRINCIPLE: if `d ~ e` and `e` converts to ITS normal form, then `d`
converts to ITS OWN normal form — convertible diagrams have equal matrices (r2 congruence
soundness), hence syntactically equal normal forms (r2 rectangle extensionality).  The
canonical-reduction residual therefore only ever needs proving up to convertibility. -/
theorem reductionTransfersAlongConversion {sourceArity targetArity : Nat}
    {leftDiagram rightDiagram : WireDiagram sourceArity targetArity}
    (areConvertible : AreConvertibleDiagrams leftDiagram rightDiagram)
    (doesRightReduce : AreConvertibleDiagrams rightDiagram
      (normalFormOfDiagram rightDiagram)) :
    AreConvertibleDiagrams leftDiagram (normalFormOfDiagram leftDiagram) := by
  have formsCoincide : normalFormOfDiagram leftDiagram = normalFormOfDiagram rightDiagram :=
    equalMatricesGiveEqualNormalForms leftDiagram rightDiagram
      (convertibleDiagramsDenoteEqualMatrices areConvertible)
  rw [formsCoincide]
  exact AreConvertibleDiagrams.fromTransitivity areConvertible doesRightReduce

/-- Normalization is syntactically IDEMPOTENT: the normal form of a canonical diagram is that
canonical diagram (r2 soundness feeds r2 rectangle extensionality). -/
theorem canonicalFormIsItsOwnNormalForm (sourceArity targetArity : Nat)
    (entries : MatrixEntries) :
    normalFormOfDiagram (canonicalDiagramOfEntries sourceArity targetArity entries)
      = canonicalDiagramOfEntries sourceArity targetArity entries :=
  canonicalDiagramRespectsRectangleAgreement sourceArity targetArity
    (denoteEntries (canonicalDiagramOfEntries sourceArity targetArity entries)) entries
    (pointwiseOfAgreeUpTo targetArity sourceArity
      (denoteEntries (canonicalDiagramOfEntries sourceArity targetArity entries)) entries
      (canonicalFormIsSoundOverMatrices sourceArity targetArity entries))

/-- THE FIXED-POINT FAMILY: every canonical diagram satisfies the canonical-reduction statement
— an infinite family of instances of the residual, for ALL arities and ALL matrices. -/
theorem canonicalDiagramSatisfiesCanonicalReduction (sourceArity targetArity : Nat)
    (entries : MatrixEntries) :
    AreConvertibleDiagrams (canonicalDiagramOfEntries sourceArity targetArity entries)
      (normalFormOfDiagram (canonicalDiagramOfEntries sourceArity targetArity entries)) := by
  rw [canonicalFormIsItsOwnNormalForm sourceArity targetArity entries]
  exact AreConvertibleDiagrams.fromReflexivity
    (canonicalDiagramOfEntries sourceArity targetArity entries)

/-- Every zero-source diagram's normal form is the bare zero stack (definitional: the canonical
construction at source arity 0 never consults the matrix). -/
theorem zeroSourceNormalFormIsZeroStack {targetArity : Nat}
    (diagram : WireDiagram 0 targetArity) :
    normalFormOfDiagram diagram = zeroVectorDiagram targetArity := rfl

/-! ## First generator instances of the canonical-reduction statement -/

/-- The empty identity satisfies canonical reduction (its normal form IS itself). -/
theorem emptyIdentitySatisfiesCanonicalReduction :
    AreConvertibleDiagrams (WireDiagram.identityWires 0)
      (normalFormOfDiagram (WireDiagram.identityWires 0)) :=
  AreConvertibleDiagrams.fromReflexivity (WireDiagram.identityWires 0)

/-- The zero generator satisfies canonical reduction: `NF(eta)` is the one-slot zero stack
`id0 | eta`, and the pad seed converts. -/
theorem zeroGenSatisfiesCanonicalReduction :
    AreConvertibleDiagrams WireDiagram.zeroGen
      (normalFormOfDiagram WireDiagram.zeroGen) :=
  AreConvertibleDiagrams.fromSymmetry padTopEtaVanishes

/-- The discard generator satisfies canonical reduction: `NF(epsilon)` is
`(id0 | id1) ; epsilon`, reached by identity expansion plus reversed identity fusion. -/
theorem discardGenSatisfiesCanonicalReduction :
    AreConvertibleDiagrams WireDiagram.discardGen
      (normalFormOfDiagram WireDiagram.discardGen) :=
  AreConvertibleDiagrams.fromTransitivity (expandIdentityAtSource WireDiagram.discardGen)
    (AreConvertibleDiagrams.underComposeSequential
      (AreConvertibleDiagrams.fromSymmetry (AreConvertibleDiagrams.tensorIdentityFusion 0 1))
      (AreConvertibleDiagrams.fromReflexivity WireDiagram.discardGen))

/-- The bottom-padded zero generator `eta | id0` satisfies canonical reduction (pad seed to
`eta`, then the zeroGen instance — its normal form coincides with `NF(eta)` definitionally). -/
theorem bottomPaddedEtaSatisfiesCanonicalReduction :
    AreConvertibleDiagrams
      (WireDiagram.tensorParallel WireDiagram.zeroGen (WireDiagram.identityWires 0))
      (normalFormOfDiagram
        (WireDiagram.tensorParallel WireDiagram.zeroGen (WireDiagram.identityWires 0))) :=
  AreConvertibleDiagrams.fromTransitivity padBottomEtaVanishes
    zeroGenSatisfiesCanonicalReduction

/-- The top-padded discard `id0 | epsilon` satisfies canonical reduction (pad seed to
`epsilon`, then the discardGen instance — the canonical construction at one source column and
zero target rows is matrix-independent, so the two normal forms coincide definitionally). -/
theorem topPaddedDiscardSatisfiesCanonicalReduction :
    AreConvertibleDiagrams
      (WireDiagram.tensorParallel (WireDiagram.identityWires 0) WireDiagram.discardGen)
      (normalFormOfDiagram
        (WireDiagram.tensorParallel (WireDiagram.identityWires 0) WireDiagram.discardGen)) :=
  AreConvertibleDiagrams.fromTransitivity padTopDiscardVanishes
    discardGenSatisfiesCanonicalReduction

/-- The scale tower fed by a zero satisfies canonical reduction, at scale factor 3 — a
seven-generator diagram reduced to the one-slot zero stack. -/
theorem scaledEtaSatisfiesCanonicalReduction :
    AreConvertibleDiagrams
      (WireDiagram.composeSequential WireDiagram.zeroGen (scaleWire 3))
      (normalFormOfDiagram
        (WireDiagram.composeSequential WireDiagram.zeroGen (scaleWire 3))) :=
  AreConvertibleDiagrams.fromTransitivity (scaleWireAbsorbsEta 3)
    (AreConvertibleDiagrams.fromSymmetry padTopEtaVanishes)

/-- The folded eta pair `(eta | eta) ; mu` satisfies canonical reduction. -/
theorem etaPairFoldSatisfiesCanonicalReduction :
    AreConvertibleDiagrams
      (WireDiagram.composeSequential
        (WireDiagram.tensorParallel WireDiagram.zeroGen WireDiagram.zeroGen)
        WireDiagram.addGen)
      (normalFormOfDiagram
        (WireDiagram.composeSequential
          (WireDiagram.tensorParallel WireDiagram.zeroGen WireDiagram.zeroGen)
          WireDiagram.addGen)) :=
  AreConvertibleDiagrams.fromTransitivity addFoldsEtaPair
    (AreConvertibleDiagrams.fromSymmetry padTopEtaVanishes)

/-! ## The reassociation fire: the right-nested eta triple

The canonical zero stack is LEFT-nested; the right-nested triple `eta | (eta | eta)` reaches it
only across a genuine tensor-tree reassociation.  The congruence carries no associativity law —
the crossing is content-mediated: B2 turns the inner pair into `eta ; delta`, coassociativity
(C1) re-brackets, B2 turns it back.  This is the mechanism (2) of THE WALL working where it CAN:
every block adjacent to the moving bracket has a zero boundary. -/

/-- The right-nested eta triple. -/
def rightNestedEtaTriple : WireDiagram 0 3 :=
  WireDiagram.tensorParallel WireDiagram.zeroGen
    (WireDiagram.tensorParallel WireDiagram.zeroGen WireDiagram.zeroGen)

/-- The LEFT-nested eta triple converts to the RIGHT-nested one — tensor reassociation
derived through B2 + coassociativity (no associativity law exists in the congruence). -/
theorem etaTripleReassociates :
    AreConvertibleDiagrams
      (WireDiagram.tensorParallel
        (WireDiagram.tensorParallel WireDiagram.zeroGen WireDiagram.zeroGen)
        WireDiagram.zeroGen)
      rightNestedEtaTriple :=
  have collapseInner : AreConvertibleDiagrams
      (WireDiagram.tensorParallel
        (WireDiagram.tensorParallel WireDiagram.zeroGen WireDiagram.zeroGen)
        WireDiagram.zeroGen)
      (WireDiagram.tensorParallel
        (WireDiagram.composeSequential WireDiagram.zeroGen WireDiagram.copyGen)
        (WireDiagram.composeSequential WireDiagram.zeroGen singleWire)) :=
    AreConvertibleDiagrams.underTensorParallel
      (AreConvertibleDiagrams.fromSymmetry AreConvertibleDiagrams.fromCopyAfterZeroBimonoidRow)
      (expandIdentityAtTarget WireDiagram.zeroGen)
  have interchangeFirst : AreConvertibleDiagrams
      (WireDiagram.tensorParallel
        (WireDiagram.composeSequential WireDiagram.zeroGen WireDiagram.copyGen)
        (WireDiagram.composeSequential WireDiagram.zeroGen singleWire))
      (WireDiagram.composeSequential
        (WireDiagram.tensorParallel WireDiagram.zeroGen WireDiagram.zeroGen)
        (WireDiagram.tensorParallel WireDiagram.copyGen singleWire)) :=
    AreConvertibleDiagrams.middleFourInterchange WireDiagram.zeroGen WireDiagram.copyGen
      WireDiagram.zeroGen singleWire
  have collapseOuter : AreConvertibleDiagrams
      (WireDiagram.composeSequential
        (WireDiagram.tensorParallel WireDiagram.zeroGen WireDiagram.zeroGen)
        (WireDiagram.tensorParallel WireDiagram.copyGen singleWire))
      (WireDiagram.composeSequential
        (WireDiagram.composeSequential WireDiagram.zeroGen WireDiagram.copyGen)
        (WireDiagram.tensorParallel WireDiagram.copyGen singleWire)) :=
    AreConvertibleDiagrams.underComposeSequential
      (AreConvertibleDiagrams.fromSymmetry AreConvertibleDiagrams.fromCopyAfterZeroBimonoidRow)
      (AreConvertibleDiagrams.fromReflexivity
        (WireDiagram.tensorParallel WireDiagram.copyGen singleWire))
  have regroupLeft : AreConvertibleDiagrams
      (WireDiagram.composeSequential
        (WireDiagram.composeSequential WireDiagram.zeroGen WireDiagram.copyGen)
        (WireDiagram.tensorParallel WireDiagram.copyGen singleWire))
      (WireDiagram.composeSequential WireDiagram.zeroGen
        (WireDiagram.composeSequential WireDiagram.copyGen
          (WireDiagram.tensorParallel WireDiagram.copyGen singleWire))) :=
    AreConvertibleDiagrams.composeReassociate WireDiagram.zeroGen WireDiagram.copyGen
      (WireDiagram.tensorParallel WireDiagram.copyGen singleWire)
  have fireCoassociativity : AreConvertibleDiagrams
      (WireDiagram.composeSequential WireDiagram.zeroGen
        (WireDiagram.composeSequential WireDiagram.copyGen
          (WireDiagram.tensorParallel WireDiagram.copyGen singleWire)))
      (WireDiagram.composeSequential WireDiagram.zeroGen
        (WireDiagram.composeSequential WireDiagram.copyGen
          (WireDiagram.tensorParallel singleWire WireDiagram.copyGen))) :=
    AreConvertibleDiagrams.underComposeSequential
      (AreConvertibleDiagrams.fromReflexivity WireDiagram.zeroGen)
      AreConvertibleDiagrams.fromCopyCoassociativityRow
  have regroupRight : AreConvertibleDiagrams
      (WireDiagram.composeSequential WireDiagram.zeroGen
        (WireDiagram.composeSequential WireDiagram.copyGen
          (WireDiagram.tensorParallel singleWire WireDiagram.copyGen)))
      (WireDiagram.composeSequential
        (WireDiagram.composeSequential WireDiagram.zeroGen WireDiagram.copyGen)
        (WireDiagram.tensorParallel singleWire WireDiagram.copyGen)) :=
    AreConvertibleDiagrams.fromSymmetry
      (AreConvertibleDiagrams.composeReassociate WireDiagram.zeroGen WireDiagram.copyGen
        (WireDiagram.tensorParallel singleWire WireDiagram.copyGen))
  have expandOuter : AreConvertibleDiagrams
      (WireDiagram.composeSequential
        (WireDiagram.composeSequential WireDiagram.zeroGen WireDiagram.copyGen)
        (WireDiagram.tensorParallel singleWire WireDiagram.copyGen))
      (WireDiagram.composeSequential
        (WireDiagram.tensorParallel WireDiagram.zeroGen WireDiagram.zeroGen)
        (WireDiagram.tensorParallel singleWire WireDiagram.copyGen)) :=
    AreConvertibleDiagrams.underComposeSequential
      AreConvertibleDiagrams.fromCopyAfterZeroBimonoidRow
      (AreConvertibleDiagrams.fromReflexivity
        (WireDiagram.tensorParallel singleWire WireDiagram.copyGen))
  have interchangeBack : AreConvertibleDiagrams
      (WireDiagram.composeSequential
        (WireDiagram.tensorParallel WireDiagram.zeroGen WireDiagram.zeroGen)
        (WireDiagram.tensorParallel singleWire WireDiagram.copyGen))
      (WireDiagram.tensorParallel
        (WireDiagram.composeSequential WireDiagram.zeroGen singleWire)
        (WireDiagram.composeSequential WireDiagram.zeroGen WireDiagram.copyGen)) :=
    AreConvertibleDiagrams.fromSymmetry
      (AreConvertibleDiagrams.middleFourInterchange WireDiagram.zeroGen singleWire
        WireDiagram.zeroGen WireDiagram.copyGen)
  have expandInner : AreConvertibleDiagrams
      (WireDiagram.tensorParallel
        (WireDiagram.composeSequential WireDiagram.zeroGen singleWire)
        (WireDiagram.composeSequential WireDiagram.zeroGen WireDiagram.copyGen))
      rightNestedEtaTriple :=
    AreConvertibleDiagrams.underTensorParallel
      (AreConvertibleDiagrams.composeIdentityTarget WireDiagram.zeroGen)
      AreConvertibleDiagrams.fromCopyAfterZeroBimonoidRow
  AreConvertibleDiagrams.fromTransitivity collapseInner
    (AreConvertibleDiagrams.fromTransitivity interchangeFirst
      (AreConvertibleDiagrams.fromTransitivity collapseOuter
        (AreConvertibleDiagrams.fromTransitivity regroupLeft
          (AreConvertibleDiagrams.fromTransitivity fireCoassociativity
            (AreConvertibleDiagrams.fromTransitivity regroupRight
              (AreConvertibleDiagrams.fromTransitivity expandOuter
                (AreConvertibleDiagrams.fromTransitivity interchangeBack expandInner)))))))

/-- THE REASSOCIATION FIRE: the right-nested eta triple satisfies canonical reduction — its
normal form is the LEFT-nested zero stack `Z 3`, reached across the content-mediated
reassociation plus the pad seed. -/
theorem rightNestedEtaTripleSatisfiesCanonicalReduction :
    AreConvertibleDiagrams rightNestedEtaTriple
      (normalFormOfDiagram rightNestedEtaTriple) :=
  AreConvertibleDiagrams.fromTransitivity
    (AreConvertibleDiagrams.fromSymmetry etaTripleReassociates)
    (AreConvertibleDiagrams.underTensorParallel
      (AreConvertibleDiagrams.underTensorParallel
        (AreConvertibleDiagrams.fromSymmetry padTopEtaVanishes)
        (AreConvertibleDiagrams.fromReflexivity WireDiagram.zeroGen))
      (AreConvertibleDiagrams.fromReflexivity WireDiagram.zeroGen))

/-! ## The swap fire: a tau-conjugated eta pair -/

/-- The swap-conjugated eta pair `(eta | eta) ; tau`. -/
def swappedEtaPairDiagram : WireDiagram 0 2 :=
  WireDiagram.composeSequential
    (WireDiagram.tensorParallel WireDiagram.zeroGen WireDiagram.zeroGen) WireDiagram.swapGen

/-- The swap-conjugated eta pair converts back to the bare pair (extrusion, then the
tau-at-eta naturality row Neta, then the mirror extrusion reversed). -/
theorem swappedEtaPairDropsSwap :
    AreConvertibleDiagrams swappedEtaPairDiagram
      (WireDiagram.tensorParallel WireDiagram.zeroGen WireDiagram.zeroGen) :=
  have extrude : AreConvertibleDiagrams swappedEtaPairDiagram
      (WireDiagram.composeSequential
        (WireDiagram.composeSequential WireDiagram.zeroGen
          (WireDiagram.tensorParallel WireDiagram.zeroGen singleWire))
        WireDiagram.swapGen) :=
    AreConvertibleDiagrams.underComposeSequential etaTensorEtaAsChain
      (AreConvertibleDiagrams.fromReflexivity WireDiagram.swapGen)
  have regroup : AreConvertibleDiagrams
      (WireDiagram.composeSequential
        (WireDiagram.composeSequential WireDiagram.zeroGen
          (WireDiagram.tensorParallel WireDiagram.zeroGen singleWire))
        WireDiagram.swapGen)
      (WireDiagram.composeSequential WireDiagram.zeroGen
        (WireDiagram.composeSequential
          (WireDiagram.tensorParallel WireDiagram.zeroGen singleWire) WireDiagram.swapGen)) :=
    AreConvertibleDiagrams.composeReassociate WireDiagram.zeroGen
      (WireDiagram.tensorParallel WireDiagram.zeroGen singleWire) WireDiagram.swapGen
  have fireNaturality : AreConvertibleDiagrams
      (WireDiagram.composeSequential WireDiagram.zeroGen
        (WireDiagram.composeSequential
          (WireDiagram.tensorParallel WireDiagram.zeroGen singleWire) WireDiagram.swapGen))
      (WireDiagram.composeSequential WireDiagram.zeroGen
        (WireDiagram.tensorParallel singleWire WireDiagram.zeroGen)) :=
    AreConvertibleDiagrams.underComposeSequential
      (AreConvertibleDiagrams.fromReflexivity WireDiagram.zeroGen)
      AreConvertibleDiagrams.fromSwapPastZeroNaturalityRow
  AreConvertibleDiagrams.fromTransitivity extrude
    (AreConvertibleDiagrams.fromTransitivity regroup
      (AreConvertibleDiagrams.fromTransitivity fireNaturality
        (AreConvertibleDiagrams.fromSymmetry etaTensorEtaAsChainMirror)))

/-- THE SWAP FIRE: the swap-conjugated eta pair satisfies canonical reduction (the tau
naturality row Neta consumed inside a genuine multi-step conversion). -/
theorem swappedEtaPairSatisfiesCanonicalReduction :
    AreConvertibleDiagrams swappedEtaPairDiagram
      (normalFormOfDiagram swappedEtaPairDiagram) :=
  AreConvertibleDiagrams.fromTransitivity swappedEtaPairDropsSwap
    (AreConvertibleDiagrams.underTensorParallel
      (AreConvertibleDiagrams.fromSymmetry padTopEtaVanishes)
      (AreConvertibleDiagrams.fromReflexivity WireDiagram.zeroGen))

/-! ## Conditional Stage-4 fires — the r30 defensive pairs' reductions, dependency-exact

The unit pair and the associativity pair ARE convertible (single row firings, shipped in r1).
Their canonical REDUCTIONS each transfer to exactly ONE remaining dependency, machine-recorded
here — no fabricated closure. -/

/-- The unit pair's canonical reduction follows from the single-wire identity's canonical
reduction (the exact remaining dependency, via the transfer principle). -/
theorem unitPairReductionFollowsFromIdentityReduction
    (doesIdentityReduce : AreConvertibleDiagrams (WireDiagram.identityWires 1)
      (normalFormOfDiagram (WireDiagram.identityWires 1))) :
    AreConvertibleDiagrams refutedUnitPairLeftSide
      (normalFormOfDiagram refutedUnitPairLeftSide) :=
  reductionTransfersAlongConversion refutedUnitPairIsNowConvertible doesIdentityReduce

/-- The associativity pair's left side reduces once its right side does (transfer along the
row conversion). -/
theorem associativityPairReductionTransfersAcrossSides
    (doesRightSideReduce : AreConvertibleDiagrams refutedAssociativityPairRightSide
      (normalFormOfDiagram refutedAssociativityPairRightSide)) :
    AreConvertibleDiagrams refutedAssociativityPairLeftSide
      (normalFormOfDiagram refutedAssociativityPairLeftSide) :=
  reductionTransfersAlongConversion refutedAssociativityPairIsNowConvertible
    doesRightSideReduce

/-! ## Kernel pins (rfl) and compiled #eval fires -/

/-- Pin: the right-nested triple's normal form IS the left-nested zero stack (kernel rfl). -/
theorem rightNestedEtaTripleNormalFormIsZeroStack :
    normalFormOfDiagram rightNestedEtaTriple = zeroVectorDiagram 3 := rfl

/-- Pin: the swapped pair's normal form is the two-slot zero stack (kernel rfl). -/
theorem swappedEtaPairNormalFormIsZeroStack :
    normalFormOfDiagram swappedEtaPairDiagram = zeroVectorDiagram 2 := rfl

/-- Pin: the 2x2 nontrivial canonical instance — the canonical diagram of the SWAP matrix
(a genuine 2-input/2-output diagram) passes the decision against its own normal form, and its
reduction is the fixed-point family member at the swap matrix. -/
theorem canonicalSwapDiagramDecisionFires :
    decideEqualMatricesOfDiagrams (canonicalDiagramOfEntries 2 2 swapGenEntries)
      (normalFormOfDiagram (canonicalDiagramOfEntries 2 2 swapGenEntries)) = true := rfl

/-- Pin: the scaled-eta fire's endpoint matrices agree via congruence soundness (consumption
of the new conversion through the r2 soundness theorem, not kernel computation). -/
theorem scaledEtaMatricesAgreeViaSoundness :
    doEntriesAgreeUpTo 1 0
      (denoteEntries (WireDiagram.composeSequential WireDiagram.zeroGen (scaleWire 3)))
      (denoteEntries WireDiagram.zeroGen) = true :=
  convertibleDiagramsDenoteEqualMatrices (scaleWireAbsorbsEta 3)

#eval decide (decideEqualMatricesOfDiagrams rightNestedEtaTriple
  (normalFormOfDiagram rightNestedEtaTriple) = true)
#eval decide (decideEqualMatricesOfDiagrams swappedEtaPairDiagram
  (normalFormOfDiagram swappedEtaPairDiagram) = true)
#eval decide (decideEqualMatricesOfDiagrams
  (WireDiagram.composeSequential WireDiagram.zeroGen (scaleWire 3)) WireDiagram.zeroGen = true)
#eval decide (decideEqualMatricesOfDiagrams (canonicalDiagramOfEntries 2 2 swapGenEntries)
  (normalFormOfDiagram (canonicalDiagramOfEntries 2 2 swapGenEntries)) = true)
#eval decide (decideEqualMatricesOfDiagrams
  (WireDiagram.composeSequential
    (WireDiagram.tensorParallel WireDiagram.zeroGen WireDiagram.zeroGen) WireDiagram.addGen)
  WireDiagram.zeroGen = true)

/-! ## THE DECISION — the anomaly-parity invariant and the refutation of the residual

The four failed attacks on padding coherence (header) suggested a conserved quantity.  Here it
is, machine-checked: a Z2 parity on tensor boundaries.  Weight a tensor node's boundary pair
`(topArity, bottomArity)` as anomalous exactly when `topArity = 0` and `bottomArity >= 2`; a
diagram's flag is the XOR of its two boundary-pair weights over all tensor nodes, XORed with
nothing else (generators and identities weigh nothing; composition adds).

WHY IT IS INVARIANT: composition-multiplicativity makes the category laws free; the tensor
weight is a COBOUNDARY in the boundary data (`source-pair weight XOR target-pair weight`), so
the middle-four interchange telescopes (the shared middle pair cancels) and identity fusion
cancels (an endo-tensor's two pairs coincide); and ALL 18 relation rows compute to
parity-equal sides (kernel rfl, one per row inside the induction) — the rows' tensor
boundaries only ever touch the pairs (0,0), (0,1), (1,0), (1,1), (1,2), (2,1), (1,3), (2,2),
none anomalous.  The weight was solved from the row constraints: the general coboundary
`theta(a,b)` must satisfy `theta(0,1) = theta(1,0) = theta(0,0)` and `theta(1,2) = theta(2,1)`
and NOTHING ELSE, leaving `theta(0,2)` free — the refutation lives in that freedom.

WHY IT REFUTES: `id0 | delta` (statable because `0+1` and `0+2` are definitionally `1` and
`2`) carries exactly ONE anomalous pair — its target pair `(0,2)` — so its flag is `true`;
every canonical diagram's flag is `false` (the only anomalous window in the whole normal-form
machine is the `id0 | gadget` rung of the one-output fan, an ENDO-tensor whose two pairs
cancel).  Convertible diagrams share the flag; hence `id0 | delta` does NOT convert to its
normal form, and `canonicalReductionStatement` is FALSE.  Worse: `id0 | delta` and bare
`delta` have EQUAL matrices (kernel rfl) and DISTINCT flags, so `matNatCompletenessStatement`
is FALSE too — the first equal-matrix non-convertible pair of the lane, the exact dual of the
Z2-pair negative control (which had distinct matrices).

WHAT IT MEANS: the 28-constructor congruence presents a structure that is NOT strict-monoidal
— the tensor unit and associator coherences are neither derivable (this refutation) nor even
STATABLE cast-free for open arities (`0 + a` and `(a+b)+c` are not definitional Nat normal
forms; only literal-right instances such as `id0 | delta ~ delta` typecheck, and those are now
refuted).  [Lafont2003] Theorem 5 is a theorem about the PROP Mat(N); the transcription's
congruence generates strictly less than the PROP quotient.  REPAIR BILL (next round's
commission material, none of it done here): either (i) add strictness rows carrying explicit
`Eq.rec` casts over own-kit Nat equalities (`zero_add`, `add_assoc`), or (ii) rebuild the
syntax unbiased/strict (flat layer lists, PROP-style objects-as-Nat with definitional
concatenation), or (iii) restate completeness against the padding-quotient (convertibility up
to anomaly-free re-bracketing).  The owner-false Props stay exactly as shipped — refuted, not
flipped. -/

/-- Parity XOR on Bool flags (own kit; `cond`-based, no library lemmas). -/
def xorParity (leftFlag rightFlag : Bool) : Bool := cond leftFlag (not rightFlag) rightFlag

/-- Is a tensor boundary pair anomalous — empty on top, at least two strands below?  The
solved-for coboundary weight: the row constraints pin `(0,0) ~ (0,1) ~ (1,0)` and
`(1,2) ~ (2,1)` but leave `(0, >=2)` free, and the congruence conserves its parity. -/
def isAnomalousBoundaryPair (topArity bottomArity : Nat) : Bool :=
  Nat.beq topArity 0 && Nat.ble 2 bottomArity

/-- Does the diagram carry an ODD number of anomalous tensor-boundary pairs?  Each tensor node
contributes its source-pair weight XOR its target-pair weight (a coboundary — this is what
makes interchange and fusion invariant); composition XORs; identities and generators carry
nothing. -/
def hasOddAnomalousBoundaryCount : {sourceArity targetArity : Nat} ->
    WireDiagram sourceArity targetArity -> Bool
  | _, _, WireDiagram.identityWires _ => false
  | _, _, WireDiagram.composeSequential firstStage secondStage =>
      xorParity (hasOddAnomalousBoundaryCount firstStage)
        (hasOddAnomalousBoundaryCount secondStage)
  | _, _, @WireDiagram.tensorParallel topSourceArity topTargetArity
      bottomSourceArity bottomTargetArity topDiagram bottomDiagram =>
      xorParity
        (xorParity (hasOddAnomalousBoundaryCount topDiagram)
          (hasOddAnomalousBoundaryCount bottomDiagram))
        (xorParity (isAnomalousBoundaryPair topSourceArity bottomSourceArity)
          (isAnomalousBoundaryPair topTargetArity bottomTargetArity))
  | _, _, WireDiagram.addGen => false
  | _, _, WireDiagram.zeroGen => false
  | _, _, WireDiagram.copyGen => false
  | _, _, WireDiagram.discardGen => false
  | _, _, WireDiagram.swapGen => false

/-- XOR with a false right flag is the identity. -/
theorem xorParityFalseRight : (flag : Bool) -> xorParity flag false = flag
  | true => rfl
  | false => rfl

/-- XOR of a flag with itself cancels. -/
theorem xorParitySelfCancels : (flag : Bool) -> xorParity flag flag = false
  | true => rfl
  | false => rfl

/-- XOR is associative (full enumeration). -/
theorem xorParityAssoc : (firstFlag secondFlag thirdFlag : Bool) ->
    xorParity (xorParity firstFlag secondFlag) thirdFlag
      = xorParity firstFlag (xorParity secondFlag thirdFlag)
  | true, true, true => rfl
  | true, true, false => rfl
  | true, false, true => rfl
  | true, false, false => rfl
  | false, true, true => rfl
  | false, true, false => rfl
  | false, false, true => rfl
  | false, false, false => rfl

/-- The middle-four-interchange XOR shuffle: the shared middle weight cancels (Bool
case-bash over all seven flags). -/
theorem xorParityInterchangeShuffle
    (firstTopFlag secondTopFlag firstBottomFlag secondBottomFlag
      sourceWeight middleWeight targetWeight : Bool) :
    xorParity
        (xorParity (xorParity firstTopFlag secondTopFlag)
          (xorParity firstBottomFlag secondBottomFlag))
        (xorParity sourceWeight targetWeight)
      = xorParity
          (xorParity (xorParity firstTopFlag firstBottomFlag)
            (xorParity sourceWeight middleWeight))
          (xorParity (xorParity secondTopFlag secondBottomFlag)
            (xorParity middleWeight targetWeight)) := by
  cases firstTopFlag <;> cases secondTopFlag <;> cases firstBottomFlag <;>
    cases secondBottomFlag <;> cases sourceWeight <;> cases middleWeight <;>
    cases targetWeight <;> rfl

/-- THE INVARIANCE THEOREM: convertible diagrams have EQUAL anomaly parity — induction over
all 28 congruence constructors (structural cases by XOR algebra, the 18 rows by kernel rfl). -/
theorem convertibleDiagramsShareAnomalyParity {sourceArity targetArity : Nat}
    {leftDiagram rightDiagram : WireDiagram sourceArity targetArity}
    (areConvertible : AreConvertibleDiagrams leftDiagram rightDiagram) :
    hasOddAnomalousBoundaryCount leftDiagram = hasOddAnomalousBoundaryCount rightDiagram := by
  induction areConvertible with
  | fromReflexivity _ => rfl
  | fromSymmetry _ flippedAgree => exact flippedAgree.symm
  | fromTransitivity _ _ leftAgree rightAgree => exact leftAgree.trans rightAgree
  | underComposeSequential _ _ firstAgree secondAgree =>
      show xorParity _ _ = xorParity _ _
      rw [firstAgree, secondAgree]
  | underTensorParallel _ _ topAgree bottomAgree =>
      show xorParity (xorParity _ _) _ = xorParity (xorParity _ _) _
      rw [topAgree, bottomAgree]
  | composeIdentitySource _ => rfl
  | composeIdentityTarget diagram =>
      exact xorParityFalseRight (hasOddAnomalousBoundaryCount diagram)
  | composeReassociate firstStage secondStage thirdStage =>
      exact xorParityAssoc (hasOddAnomalousBoundaryCount firstStage)
        (hasOddAnomalousBoundaryCount secondStage)
        (hasOddAnomalousBoundaryCount thirdStage)
  | tensorIdentityFusion topStrandCount bottomStrandCount =>
      exact xorParitySelfCancels (isAnomalousBoundaryPair topStrandCount bottomStrandCount)
  | @middleFourInterchange topSourceArity topMiddleArity topTargetArity
      bottomSourceArity bottomMiddleArity bottomTargetArity
      topFirst topSecond bottomFirst bottomSecond =>
      exact xorParityInterchangeShuffle
        (hasOddAnomalousBoundaryCount topFirst) (hasOddAnomalousBoundaryCount topSecond)
        (hasOddAnomalousBoundaryCount bottomFirst) (hasOddAnomalousBoundaryCount bottomSecond)
        (isAnomalousBoundaryPair topSourceArity bottomSourceArity)
        (isAnomalousBoundaryPair topMiddleArity bottomMiddleArity)
        (isAnomalousBoundaryPair topTargetArity bottomTargetArity)
  | fromAddAssociativityRow => rfl
  | fromAddLeftUnitRow => rfl
  | fromAddRightUnitRow => rfl
  | fromAddCommutativityRow => rfl
  | fromCopyCoassociativityRow => rfl
  | fromCopyLeftCounitRow => rfl
  | fromCopyRightCounitRow => rfl
  | fromCopyCocommutativityRow => rfl
  | fromCopyAfterAddBimonoidRow => rfl
  | fromCopyAfterZeroBimonoidRow => rfl
  | fromDiscardAfterAddBimonoidRow => rfl
  | fromDiscardAfterZeroBimonoidRow => rfl
  | fromSwapInvolutionRow => rfl
  | fromSwapYangBaxterRow => rfl
  | fromSwapPastAddNaturalityRow => rfl
  | fromSwapPastZeroNaturalityRow => rfl
  | fromCopyPastSwapNaturalityRow => rfl
  | fromDiscardPastSwapNaturalityRow => rfl

/-! ### The separator and the refutation theorems -/

/-- THE SEPARATOR: the top-padded copy `id0 | delta` — the statable strictness instance
(`0+1` and `0+2` are definitionally `1` and `2`). -/
def leftPaddedCopyDiagram : WireDiagram 1 2 :=
  WireDiagram.tensorParallel (WireDiagram.identityWires 0) WireDiagram.copyGen

/-- The separator carries ODD anomaly parity — its single tensor node has source pair (0,1)
(weight 0) and target pair (0,2) (weight 1). -/
theorem leftPaddedCopyHasOddAnomaly :
    hasOddAnomalousBoundaryCount leftPaddedCopyDiagram = true := rfl

/-- The separator's NORMAL FORM carries EVEN anomaly parity (kernel computation through the
whole normal-form machine: the only anomalous window, the `id0 | gadget` rung, is an
endo-tensor and cancels). -/
theorem leftPaddedCopyNormalFormHasEvenAnomaly :
    hasOddAnomalousBoundaryCount (normalFormOfDiagram leftPaddedCopyDiagram) = false := rfl

/-- Bare copy carries even anomaly parity. -/
theorem copyGenHasEvenAnomaly :
    hasOddAnomalousBoundaryCount WireDiagram.copyGen = false := rfl

/-- The separator does NOT convert to its own normal form (parity clash). -/
theorem leftPaddedCopyDoesNotReduceToItsNormalForm :
    AreConvertibleDiagrams leftPaddedCopyDiagram
      (normalFormOfDiagram leftPaddedCopyDiagram) -> False :=
  fun wouldReduce =>
    Bool.noConfusion
      ((leftPaddedCopyHasOddAnomaly.symm.trans
        (convertibleDiagramsShareAnomalyParity wouldReduce)).trans
        leftPaddedCopyNormalFormHasEvenAnomaly)

/-- THE DECISION, part 1: `canonicalReductionStatement` is REFUTED — not every diagram
converts to its normal form in the shipped congruence. -/
theorem canonicalReductionStatementIsRefuted : canonicalReductionStatement -> False :=
  fun doAllDiagramsReduce =>
    leftPaddedCopyDoesNotReduceToItsNormalForm (doAllDiagramsReduce 1 2 leftPaddedCopyDiagram)

/-- The separator and bare copy denote EQUAL matrices on the full rectangle (kernel rfl) —
the pair is inside the completeness statement's hypothesis. -/
theorem leftPaddedCopyAgreesWithCopyOnMatrices :
    doEntriesAgreeUpTo 2 1 (denoteEntries leftPaddedCopyDiagram)
      (denoteEntries WireDiagram.copyGen) = true := rfl

/-- THE FIRST EQUAL-MATRIX NON-CONVERTIBLE PAIR: `id0 | delta` and `delta` denote the same
matrix yet are NOT convertible (parity clash) — the exact dual of the Z2-pair negative
control, which had distinct matrices. -/
theorem leftPaddedCopyIsNotConvertibleToBareCopy :
    AreConvertibleDiagrams leftPaddedCopyDiagram WireDiagram.copyGen -> False :=
  fun wouldConvert =>
    Bool.noConfusion
      ((leftPaddedCopyHasOddAnomaly.symm.trans
        (convertibleDiagramsShareAnomalyParity wouldConvert)).trans copyGenHasEvenAnomaly)

/-- THE DECISION, part 2: `matNatCompletenessStatement` is REFUTED — equal matrices do NOT
imply convertibility in the shipped congruence.  [Lafont2003] Theorem 5 concerns the PROP
Mat(N); the 28-constructor congruence generates strictly less than the PROP quotient (the
strictness coherences are missing — and are not even statable cast-free at open arities). -/
theorem matNatCompletenessStatementIsRefuted : matNatCompletenessStatement -> False :=
  fun isComplete =>
    leftPaddedCopyIsNotConvertibleToBareCopy
      (isComplete 1 2 leftPaddedCopyDiagram WireDiagram.copyGen
        leftPaddedCopyAgreesWithCopyOnMatrices)

/-- THE DECISION, corollary: the matrix-comparison decision procedure can NEVER be upgraded to
an unconditional convertibility affirmer over this congruence. -/
theorem decisionCompletenessIsRefuted :
    (∀ (sourceArity targetArity : Nat)
      (candidateLeft candidateRight : WireDiagram sourceArity targetArity),
      decideEqualMatricesOfDiagrams candidateLeft candidateRight = true ->
      AreConvertibleDiagrams candidateLeft candidateRight) -> False :=
  fun wouldAffirm =>
    leftPaddedCopyIsNotConvertibleToBareCopy
      (wouldAffirm 1 2 leftPaddedCopyDiagram WireDiagram.copyGen
        leftPaddedCopyAgreesWithCopyOnMatrices)

/-- Consistency consumption: the invariance theorem agrees with a LANDED positive conversion
(the swap fire) — the parity machinery convicts only genuinely non-convertible pairs. -/
theorem anomalyParityAgreesOnLandedConversion :
    hasOddAnomalousBoundaryCount swappedEtaPairDiagram
      = hasOddAnomalousBoundaryCount (normalFormOfDiagram swappedEtaPairDiagram) :=
  convertibleDiagramsShareAnomalyParity swappedEtaPairSatisfiesCanonicalReduction

#eval decide (hasOddAnomalousBoundaryCount leftPaddedCopyDiagram = true)
#eval decide (hasOddAnomalousBoundaryCount (normalFormOfDiagram leftPaddedCopyDiagram) = false)
#eval decide (hasOddAnomalousBoundaryCount WireDiagram.copyGen = false)
#eval decide (decideEqualMatricesOfDiagrams leftPaddedCopyDiagram WireDiagram.copyGen = true)
#eval decide (hasOddAnomalousBoundaryCount (zeroVectorDiagram 3) = false)

end FX1Poly.Polygraph.Omega.LafontProp
