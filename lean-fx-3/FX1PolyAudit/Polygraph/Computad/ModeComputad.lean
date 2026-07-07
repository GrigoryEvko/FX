import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Computad.ModeComputad

/-! # FX1PolyAudit.Polygraph.Computad.ModeComputad — zero-axiom gate for the finite mode computad

Per-declaration zero-axiom gate for the FINITE first-order 2-computad presentation
(`FX1Poly/Polygraph/Computad/ModeComputad.lean`): the `ComputadTwoGen` / `ModeComputad` carrier, the
carrier-computed `dimensionProfile` / `richnessEvidence`, the reconstruction to the shipped `ModeSignature`
carrier (`Modality` / `toModeGraph` / `toModeSignatureSkeleton`), the two concrete computads, observable
faithfulness, and the genuine 0/1-skeleton iso `adjunctionComputadGraphEquiv`.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Carrier + carrier-computed richness data
#assert_no_axioms FX1Poly.Polygraph.ComputadTwoGen
#assert_no_axioms FX1Poly.Polygraph.ModeComputad
#assert_no_axioms FX1Poly.Polygraph.ModeComputad.dimensionProfile
#assert_no_axioms FX1Poly.Polygraph.ModeComputad.richnessEvidence

-- Reconstruction into the shipped carrier
#assert_no_axioms FX1Poly.Polygraph.ModeComputad.Modality
#assert_no_axioms FX1Poly.Polygraph.ModeComputad.toModeGraph
#assert_no_axioms FX1Poly.Polygraph.ModeComputad.toModeSignatureSkeleton

-- The TOTAL word-to-ModalityPath interpreter (task 2A-i)
#assert_no_axioms FX1Poly.Polygraph.ModeComputad.interpretWordFrom
#assert_no_axioms FX1Poly.Polygraph.ModeComputad.ReconstructedTwoCell
#assert_no_axioms FX1Poly.Polygraph.ModeComputad.toModeSignature
#assert_no_axioms FX1Poly.Polygraph.ModeComputad.toModeSignature_graph

-- Dimension-2 faithfulness: reconstructed unit / counit 2-cells
#assert_no_axioms FX1Poly.Polygraph.adjunctionComputadReconstructedLeftThenRight
#assert_no_axioms FX1Poly.Polygraph.adjunctionComputadReconstructedRightThenLeft
#assert_no_axioms FX1Poly.Polygraph.adjunctionComputad_reconstructsUnit
#assert_no_axioms FX1Poly.Polygraph.adjunctionComputad_reconstructsCounit

-- The two concrete computads
#assert_no_axioms FX1Poly.Polygraph.singleObjectSemiringComputad
#assert_no_axioms FX1Poly.Polygraph.adjunctionComputadModalityGenerators
#assert_no_axioms FX1Poly.Polygraph.adjunctionComputad

-- Observable faithfulness
#assert_no_axioms FX1Poly.Polygraph.adjunctionModeToFin
#assert_no_axioms FX1Poly.Polygraph.adjunctionSignatureGeneratorEndpoints
#assert_no_axioms FX1Poly.Polygraph.adjunctionComputad_generators_faithful
#assert_no_axioms FX1Poly.Polygraph.adjunctionComputad_twoCellCount_faithful
#assert_no_axioms FX1Poly.Polygraph.singleObjectSemiringComputad_shape

-- The Type-level faithfulness iso
#assert_no_axioms FX1Poly.Polygraph.TypeEquiv
#assert_no_axioms FX1Poly.Polygraph.ModeGraphEquiv
#assert_no_axioms FX1Poly.Polygraph.adjunctionFinToMode
#assert_no_axioms FX1Poly.Polygraph.adjunctionComputadModeEquiv
#assert_no_axioms FX1Poly.Polygraph.adjunctionComputad_onlyIndexZeroIsBaseTip
#assert_no_axioms FX1Poly.Polygraph.adjunctionComputad_onlyIndexOneIsTipBase
#assert_no_axioms FX1Poly.Polygraph.adjunctionComputad_noGeneratorIsBaseBase
#assert_no_axioms FX1Poly.Polygraph.adjunctionComputad_noGeneratorIsTipTip
#assert_no_axioms FX1Poly.Polygraph.adjunctionComputadModalityEquiv
#assert_no_axioms FX1Poly.Polygraph.adjunctionComputadGraphEquiv

-- Honesty markers
#assert_no_axioms FX1Poly.Polygraph.polygraph_hasModeComputad
#assert_no_axioms FX1Poly.Polygraph.polygraph_hasTotalModeSignatureInterpreter

end FX1PolyAudit
