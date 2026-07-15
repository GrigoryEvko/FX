import FX1Poly.Polygraph.Omega.LafontProp.ConvertibilitySoundness

/-! # Polygraph/Omega/LafontProp/DiagramDecisionFires — the word-problem decision, fired
(LAFONT-PROP r2, brick C: THE DECISION FIRES)

The decision procedure for the Mat(N) word problem is MATRIX COMPARISON:
`decideEqualMatricesOfDiagrams` computes both denotations and compares them on the boundary
rectangle — a closed `Bool` the kernel evaluates by `rfl`/`decide`.  Its logical status, all
machine-checked here:

* NEGATIVE DIRECTION, UNCONDITIONAL (`decisionRefutesConvertibility`): a `false` comparison
  refutes convertibility — by the congruence soundness of brick B.
* POSITIVE DIRECTION, SOUND (`decisionIsImpliedByConvertibility`): every convertible pair
  passes the comparison.
* POSITIVE DIRECTION, COMPLETE MODULO THE NAMED RESIDUAL
  (`decisionAffirmsConvertibilityGivenCanonicalReduction`): a `true` comparison yields
  convertibility GIVEN `canonicalReductionStatement` (brick A's reduction theorem) — the one
  remaining open obligation of the lane.

THE FIRES (each pair carries a compiled `#eval decide` pin plus kernel-`rfl` theorems, and the
positive pairs carry explicit convertibility witnesses):

1. the r30 old-killer UNIT pair `(id1 | eta) ; mu` vs `id1` — decision true, one-row
   conversion, and the two normal forms are SYNTACTICALLY EQUAL by kernel `rfl`;
2. the old-killer ASSOCIATIVITY pair `(mu | id1) ; mu` vs `(id1 | mu) ; mu` — same trio;
3. a COPY/ADD SPIDER: one input copied to three strands, folded by the two add-tree
   associations — decision true, matrices `[[3]]`, conversion by congruence with the
   associativity row;
4. a SWAP-HEAVY pair: `tau ; tau ; tau` vs `tau` — decision true, two-step conversion
   (involution row under congruence, then the identity-source law); plus the Yang-Baxter pair;
5. the BIALGEBRA square (B1) pushed through the whole normal-form machine: the two sides'
   normal forms are syntactically equal by kernel `rfl`;
6. THE NEGATIVE CONTROL: the Z2-only pair `delta ; mu` vs `epsilon ; eta` ([[2]] vs [[0]]) —
   decision FALSE, and NOT CONVERTIBLE, machine-checked (`zSpecificPairIsNotConvertible`):
   the first kernel-checked non-convertibility of the lane.

Raw Lean 4 + Init only; zero-axiom; audit twin with per-decl `#assert_no_axioms` plus an
independent `#print axioms` witness. -/

namespace FX1Poly.Polygraph.Omega.LafontProp

/-! ## The decision procedure -/

/-- THE DECISION: compare the two denotations on the boundary rectangle.  Closed instances
evaluate by kernel computation. -/
def decideEqualMatricesOfDiagrams {sourceArity targetArity : Nat}
    (leftDiagram rightDiagram : WireDiagram sourceArity targetArity) : Bool :=
  doEntriesAgreeUpTo targetArity sourceArity
    (denoteEntries leftDiagram) (denoteEntries rightDiagram)

/-- Negative direction, unconditional: a failed comparison refutes convertibility. -/
theorem decisionRefutesConvertibility {sourceArity targetArity : Nat}
    (leftDiagram rightDiagram : WireDiagram sourceArity targetArity)
    (decisionFails : decideEqualMatricesOfDiagrams leftDiagram rightDiagram = false) :
    AreConvertibleDiagrams leftDiagram rightDiagram -> False :=
  notConvertibleOfDistinctMatrices leftDiagram rightDiagram decisionFails

/-- Positive direction, soundness: convertible pairs always pass the comparison. -/
theorem decisionIsImpliedByConvertibility {sourceArity targetArity : Nat}
    {leftDiagram rightDiagram : WireDiagram sourceArity targetArity}
    (areConvertible : AreConvertibleDiagrams leftDiagram rightDiagram) :
    decideEqualMatricesOfDiagrams leftDiagram rightDiagram = true :=
  convertibleDiagramsDenoteEqualMatrices areConvertible

/-- Positive direction, completeness MODULO the named residual: a passed comparison yields
convertibility given `canonicalReductionStatement`. -/
theorem decisionAffirmsConvertibilityGivenCanonicalReduction
    (doAllDiagramsReduce : canonicalReductionStatement)
    {sourceArity targetArity : Nat}
    (leftDiagram rightDiagram : WireDiagram sourceArity targetArity)
    (decisionHolds : decideEqualMatricesOfDiagrams leftDiagram rightDiagram = true) :
    AreConvertibleDiagrams leftDiagram rightDiagram :=
  completenessReducesToCanonicalReduction doAllDiagramsReduce sourceArity targetArity
    leftDiagram rightDiagram decisionHolds

/-! ## Fire 1: the old-killer unit pair -/

/-- The decision fires TRUE on the r30 refuted unit pair (kernel rfl). -/
theorem unitPairDecisionFires :
    decideEqualMatricesOfDiagrams refutedUnitPairLeftSide (WireDiagram.identityWires 1)
      = true := rfl

/-- The unit pair's normal forms are SYNTACTICALLY EQUAL (kernel rfl through the whole
normal-form machine). -/
theorem unitPairNormalFormsCoincide :
    normalFormOfDiagram refutedUnitPairLeftSide
      = normalFormOfDiagram (WireDiagram.identityWires 1) := rfl

/-- The unit pair decision is affirmed by the r1 one-row conversion (soundness consumption). -/
theorem unitPairDecisionAgreesWithConversion :
    decideEqualMatricesOfDiagrams refutedUnitPairLeftSide (WireDiagram.identityWires 1)
      = true :=
  decisionIsImpliedByConvertibility refutedUnitPairIsNowConvertible

/-! ## Fire 2: the old-killer associativity pair -/

/-- The decision fires TRUE on the refuted associativity pair (kernel rfl). -/
theorem associativityPairDecisionFires :
    decideEqualMatricesOfDiagrams refutedAssociativityPairLeftSide
      refutedAssociativityPairRightSide = true := rfl

/-- The associativity pair's normal forms coincide syntactically (kernel rfl). -/
theorem associativityPairNormalFormsCoincide :
    normalFormOfDiagram refutedAssociativityPairLeftSide
      = normalFormOfDiagram refutedAssociativityPairRightSide := rfl

/-! ## Fire 3: the copy/add spider (one wire tripled, two fold orders) -/

/-- Copy one strand into three. -/
def spiderCopyStage : WireDiagram 1 3 :=
  WireDiagram.composeSequential WireDiagram.copyGen
    (WireDiagram.tensorParallel WireDiagram.copyGen singleWire : WireDiagram 2 3)

/-- The spider folded left: copies, then `(mu | id1) ; mu`. -/
def spiderFoldedLeftSide : WireDiagram 1 1 :=
  WireDiagram.composeSequential spiderCopyStage addAssociativityLeftSide

/-- The spider folded right: copies, then `(id1 | mu) ; mu`. -/
def spiderFoldedRightSide : WireDiagram 1 1 :=
  WireDiagram.composeSequential spiderCopyStage addAssociativityRightSide

/-- The spider denotes the tripling matrix [[3]] (kernel rfl). -/
theorem spiderDenotesTripling : denoteEntries spiderFoldedLeftSide 0 0 = 3 := rfl

/-- The decision fires TRUE on the spider pair (kernel rfl). -/
theorem spiderPairDecisionFires :
    decideEqualMatricesOfDiagrams spiderFoldedLeftSide spiderFoldedRightSide = true := rfl

/-- The spider pair converts: congruence under composition with the associativity row. -/
theorem spiderPairIsConvertible :
    AreConvertibleDiagrams spiderFoldedLeftSide spiderFoldedRightSide :=
  AreConvertibleDiagrams.underComposeSequential
    (AreConvertibleDiagrams.fromReflexivity spiderCopyStage)
    AreConvertibleDiagrams.fromAddAssociativityRow

/-- The spider pair's normal forms coincide syntactically (kernel rfl). -/
theorem spiderPairNormalFormsCoincide :
    normalFormOfDiagram spiderFoldedLeftSide = normalFormOfDiagram spiderFoldedRightSide := rfl

/-! ## Fire 4: swap-heavy pairs -/

/-- Three swaps in a row. -/
def tripleSwapDiagram : WireDiagram 2 2 :=
  WireDiagram.composeSequential
    (WireDiagram.composeSequential WireDiagram.swapGen WireDiagram.swapGen)
    WireDiagram.swapGen

/-- The decision fires TRUE on `tau ; tau ; tau` vs `tau` (kernel rfl). -/
theorem tripleSwapDecisionFires :
    decideEqualMatricesOfDiagrams tripleSwapDiagram WireDiagram.swapGen = true := rfl

/-- `tau ; tau ; tau` converts to `tau`: the involution row under congruence, then the
identity-source structural law. -/
theorem tripleSwapIsConvertibleToSwap :
    AreConvertibleDiagrams tripleSwapDiagram WireDiagram.swapGen :=
  AreConvertibleDiagrams.fromTransitivity
    (AreConvertibleDiagrams.underComposeSequential
      AreConvertibleDiagrams.fromSwapInvolutionRow
      (AreConvertibleDiagrams.fromReflexivity WireDiagram.swapGen))
    (AreConvertibleDiagrams.composeIdentitySource WireDiagram.swapGen)

/-- The triple-swap normal form coincides with the swap normal form (kernel rfl). -/
theorem tripleSwapNormalFormsCoincide :
    normalFormOfDiagram tripleSwapDiagram = normalFormOfDiagram WireDiagram.swapGen := rfl

/-- The decision fires TRUE on the Yang-Baxter pair (kernel rfl); its conversion is the row. -/
theorem yangBaxterDecisionFires :
    decideEqualMatricesOfDiagrams swapYangBaxterLeftSide swapYangBaxterRightSide = true := rfl

/-- The Yang-Baxter pair's normal forms coincide syntactically (kernel rfl). -/
theorem yangBaxterNormalFormsCoincide :
    normalFormOfDiagram swapYangBaxterLeftSide
      = normalFormOfDiagram swapYangBaxterRightSide := rfl

/-! ## Fire 5: the bialgebra square through the normal-form machine -/

/-- The decision fires TRUE on the (B1) bialgebra square (kernel rfl). -/
theorem bimonoidSquareDecisionFires :
    decideEqualMatricesOfDiagrams copyAfterAddLeftSide copyAfterAddRightSide = true := rfl

/-- The (B1) square's normal forms coincide syntactically (kernel rfl) — the two-generator
side and the five-generator side canonicalize to the SAME diagram. -/
theorem bimonoidSquareNormalFormsCoincide :
    normalFormOfDiagram copyAfterAddLeftSide = normalFormOfDiagram copyAfterAddRightSide := rfl

/-! ## Fire 6: THE NEGATIVE CONTROL — the Z2-only pair is refuted -/

/-- `delta ; mu` — copy then add, the doubling map [[2]]. -/
def doublingDiagram : WireDiagram 1 1 :=
  WireDiagram.composeSequential WireDiagram.copyGen WireDiagram.addGen

/-- `epsilon ; eta` — discard then zero, the constant-zero map [[0]]. -/
def resetDiagram : WireDiagram 1 1 :=
  WireDiagram.composeSequential WireDiagram.discardGen WireDiagram.zeroGen

/-- The decision fires FALSE on the Z2-only pair (kernel rfl): [[2]] differs from [[0]]. -/
theorem zSpecificPairDecisionRefutes :
    decideEqualMatricesOfDiagrams doublingDiagram resetDiagram = false := rfl

/-- THE NON-CONVERTIBILITY FIRE: the Z2-only relation `mu . delta = eta . epsilon` ([Lafont2003]
figure 13, "specific to Z2") is NOT derivable in the Mat(N) presentation — machine-checked via
congruence soundness.  The first kernel-checked non-convertibility of the lane. -/
theorem zSpecificPairIsNotConvertible :
    AreConvertibleDiagrams doublingDiagram resetDiagram -> False :=
  decisionRefutesConvertibility doublingDiagram resetDiagram zSpecificPairDecisionRefutes

/-! ## Compiled #eval decide pins (all must print `true`) -/

#eval decide (decideEqualMatricesOfDiagrams refutedUnitPairLeftSide
  (WireDiagram.identityWires 1) = true)
#eval decide (decideEqualMatricesOfDiagrams refutedAssociativityPairLeftSide
  refutedAssociativityPairRightSide = true)
#eval decide (decideEqualMatricesOfDiagrams spiderFoldedLeftSide spiderFoldedRightSide = true)
#eval decide (denoteEntries spiderFoldedLeftSide 0 0 = 3)
#eval decide (decideEqualMatricesOfDiagrams tripleSwapDiagram WireDiagram.swapGen = true)
#eval decide (decideEqualMatricesOfDiagrams swapYangBaxterLeftSide
  swapYangBaxterRightSide = true)
#eval decide (decideEqualMatricesOfDiagrams copyAfterAddLeftSide copyAfterAddRightSide = true)
#eval decide (decideEqualMatricesOfDiagrams doublingDiagram resetDiagram = false)

end FX1Poly.Polygraph.Omega.LafontProp
