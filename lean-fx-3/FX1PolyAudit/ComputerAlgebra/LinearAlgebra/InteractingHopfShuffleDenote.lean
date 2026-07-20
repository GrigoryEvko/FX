import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.InteractingHopfShuffleDenote

/-! # FX1PolyAudit/ComputerAlgebra/LinearAlgebra/InteractingHopfShuffleDenote —
    zero-axiom gate (WP-PROP-3 brick 9: the perfect (un)shuffle denotation)

Per-declaration zero-axiom gate for:

* the width arithmetic and unshuffle arity/WF bookkeeping (`ihuWidthCanon`,
  `ihuWidthMove`, `ihuUnshuffleCodArity`, `ihuUnshuffleWF`, `ihuWhiskerACod`);
* the whisker-left pair-membership specs (`ihuWhiskerLeftSpec`,
  `ihuWhiskeredUnshuffleSpec`);
* THE UNSHUFFLE DENOTATION (T1, `ihuUnshuffleDenote`) with its residual inhabitant
  (`ihuUnshuffleDenoteHolds`), DECIDED marker (`ihuHasUnshuffleDenote`) and content
  fire (`ihuFireUnshuffleContent`);
* the propext-free reverse structure (`ihuCatLayersAssoc`, `ihuReverseAuxCat`,
  `ihuReverseConsCat`) and the crossing-self-inverse base fact
  (`ihuSwapSelfConverse`);
* the whisker single-layer spec/self-converse (`ihuWhiskerLayerLeftSpec`,
  `ihuWhiskerLayerSelfConverse`);
* the reversibility calculus (`IhuReversible` + constructors, `ihuReversibleCast`,
  `ihuReversibleWF`, `ihuReversibleCodArity`, `ihuReversibleCat`,
  `ihuReversibleReverse`, `ihuReversibleWhisker`, `ihuReversibleMoveRight`,
  `ihuReversibleUnshuffle`);
* the one-layer denote helpers (`ihuSingletonDenote`, `ihuSingletonSquareDenote`);
* THE REVERSE-IS-CONVERSE BRIDGE (`ihuReverseConverse`) and THE SHUFFLE DENOTATION
  (T1, `ihuShuffleDenote`) with its residual inhabitant (`ihuShuffleDenoteHolds`),
  DECIDED marker (`ihuHasShuffleDenote`) and content fire (`ihuFireShuffleContent`);
* the T2 / T3 walls (`ihuHasTwoRowSpatialSum`, `ihuHasNormalFormCompiler`,
  both owner false).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`, `funext`, `WellFounded.fix`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.ihuWidthCanon
#assert_no_axioms FX1Poly.ComputerAlgebra.ihuWidthMove
#assert_no_axioms FX1Poly.ComputerAlgebra.ihuUnshuffleCodArity
#assert_no_axioms FX1Poly.ComputerAlgebra.ihuUnshuffleWF
#assert_no_axioms FX1Poly.ComputerAlgebra.ihuWhiskerACod
#assert_no_axioms FX1Poly.ComputerAlgebra.ihuWhiskerLeftSpec
#assert_no_axioms FX1Poly.ComputerAlgebra.ihuWhiskeredUnshuffleSpec
#assert_no_axioms FX1Poly.ComputerAlgebra.ihuUnshuffleDenote
#assert_no_axioms FX1Poly.ComputerAlgebra.ihuUnshuffleDenoteHolds
#assert_no_axioms FX1Poly.ComputerAlgebra.ihuHasUnshuffleDenote
#assert_no_axioms FX1Poly.ComputerAlgebra.ihuFireUnshuffleContent
#assert_no_axioms FX1Poly.ComputerAlgebra.ihuCatLayersAssoc
#assert_no_axioms FX1Poly.ComputerAlgebra.ihuReverseAuxCat
#assert_no_axioms FX1Poly.ComputerAlgebra.ihuReverseConsCat
#assert_no_axioms FX1Poly.ComputerAlgebra.ihuSwapSelfConverse
#assert_no_axioms FX1Poly.ComputerAlgebra.ihuWhiskerLayerLeftSpec
#assert_no_axioms FX1Poly.ComputerAlgebra.ihuWhiskerLayerSelfConverse
#assert_no_axioms FX1Poly.ComputerAlgebra.IhuReversible
#assert_no_axioms FX1Poly.ComputerAlgebra.IhuReversible.nil
#assert_no_axioms FX1Poly.ComputerAlgebra.IhuReversible.cons
#assert_no_axioms FX1Poly.ComputerAlgebra.ihuReversibleCast
#assert_no_axioms FX1Poly.ComputerAlgebra.ihuReversibleWF
#assert_no_axioms FX1Poly.ComputerAlgebra.ihuReversibleCodArity
#assert_no_axioms FX1Poly.ComputerAlgebra.ihuReversibleCat
#assert_no_axioms FX1Poly.ComputerAlgebra.ihuReversibleReverse
#assert_no_axioms FX1Poly.ComputerAlgebra.ihuReversibleWhisker
#assert_no_axioms FX1Poly.ComputerAlgebra.ihuReversibleMoveRight
#assert_no_axioms FX1Poly.ComputerAlgebra.ihuReversibleUnshuffle
#assert_no_axioms FX1Poly.ComputerAlgebra.ihuSingletonDenote
#assert_no_axioms FX1Poly.ComputerAlgebra.ihuSingletonSquareDenote
#assert_no_axioms FX1Poly.ComputerAlgebra.ihuReverseConverse
#assert_no_axioms FX1Poly.ComputerAlgebra.ihuShuffleDenote
#assert_no_axioms FX1Poly.ComputerAlgebra.ihuShuffleDenoteHolds
#assert_no_axioms FX1Poly.ComputerAlgebra.ihuHasShuffleDenote
#assert_no_axioms FX1Poly.ComputerAlgebra.ihuFireShuffleContent
#assert_no_axioms FX1Poly.ComputerAlgebra.ihuHasTwoRowSpatialSum
#assert_no_axioms FX1Poly.ComputerAlgebra.ihuHasNormalFormCompiler

end FX1PolyAudit
