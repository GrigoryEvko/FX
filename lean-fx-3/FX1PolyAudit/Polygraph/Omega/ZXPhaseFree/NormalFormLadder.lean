import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.ZXPhaseFree.NormalFormLadder

/-! # FX1PolyAudit.Polygraph.Omega.ZXPhaseFree.NormalFormLadder — zero-axiom gate
(THE REWRITE LADDER: pad-lifting congruence + fusion up to k = 3 + THE WALL)

Per-declaration zero-axiom gate for the ladder brick: the cat/whisker composition
kit (`zxnWireCellsCat`, `zxnCatCellsAssoc`, whisker compose/cat, layer-list assoc,
`zxnPadDiagramCompose` — a pad of a pad is one composite pad), THE PAD-LIFTING
CONGRUENCE `zxnConvLift` (whole `ZxrConv` derivations lift into any padding
context), eta-expansion of wires into identity spiders of both colours (window +
in-context), left-first sequentialization of adjacent cells, PARALLEL SAME-COLOUR
FUSION at shared-wire counts 1/2/3 in both colours at all boundary arities, THE
WALL (`zxnRightFirstExchangeStatement` owner-false with the semantic-soundness
instance pin), and the honesty markers (general k-wire fusion FALSE,
colour-alternation FALSE, `zxnCompletenessViaCensusIsProven` FALSE with the
(i)-(iv) bill; `zxrCompletenessIsProven` in FusionRepair stays byte-intact FALSE).

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`,
`omega`, `WellFounded.fix`, `funext`.  Built by the FX1PolyAudit lib glob;
AuditAll registration is a later round's bookkeeping (AuditAll untouched per this
round's commission). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnWireCellsCat
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnCatCellsAssoc
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnWhiskerLayerCompose
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnWhiskerLayersCompose
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnWhiskerLayersCat
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnCatLayersAssoc
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnPadDiagramCompose
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnLiftArityShuffle
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnConvLift
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnWireDiagram
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnZIdentitySpiderDiagram
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnXIdentitySpiderDiagram
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnEtaExpandWireZ
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnEtaExpandWireX
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnEtaExpandWireZInContext
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnSequentializeAdjacentCells
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnParallelFusionOneWireZ
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnParallelFusionOneWireX
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnParallelFusionTwoWireZ
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnParallelFusionTwoWireX
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnParallelFusionThreeWireZ
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnParallelFusionThreeWireX
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnRightFirstExchangeStatement
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnRightFirstExchangeIsProven
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnRightFirstExchangeInstanceSpanPin
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnHasPadLiftingCongruence
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnLadderEtaExpansionLanded
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnLadderParallelFusionUpToThreeLanded
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnLadderGeneralKWireFusionLanded
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnLadderColourAlternationLanded
#assert_no_axioms FX1Poly.Polygraph.Omega.ZXPhaseFree.zxnCompletenessViaCensusIsProven

end FX1PolyAudit
