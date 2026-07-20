import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Net.LafontCombinators

/-! # FX1PolyAudit.Polygraph.Net.LafontCombinators — zero-axiom gate (NET-11)

Per-declaration zero-axiom gate for the Lafont interaction-combinator system: the three-symbol carrier
(`AgentKind` + agents + nets + active pairs), the six interaction rules (`icbInteract`), one-step reduction
and normal-form recognition, the local-confluence-by-orthogonality diamond, the two honest walls
(Turing-universality ⇒ undecidable global normalization), and the concrete fires.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`, `funext`,
`WellFounded.fix`.  (Not registered in `AuditAll` here — left to the umbrella owner.) -/

namespace FX1PolyAudit

-- T1: carrier — kinds, agents, nets
#assert_no_axioms FX1Poly.Polygraph.AgentKind
#assert_no_axioms FX1Poly.Polygraph.AgentKind.gammaCon
#assert_no_axioms FX1Poly.Polygraph.AgentKind.deltaDup
#assert_no_axioms FX1Poly.Polygraph.AgentKind.epsilonEra
#assert_no_axioms FX1Poly.Polygraph.icbKindBeq
#assert_no_axioms FX1Poly.Polygraph.icbAgent
#assert_no_axioms FX1Poly.Polygraph.icbAgent.mk
#assert_no_axioms FX1Poly.Polygraph.icbNet
#assert_no_axioms FX1Poly.Polygraph.icbNet.mk
#assert_no_axioms FX1Poly.Polygraph.icbPrincipalPort
#assert_no_axioms FX1Poly.Polygraph.icbAux1
#assert_no_axioms FX1Poly.Polygraph.icbAux2
#assert_no_axioms FX1Poly.Polygraph.icbFindAgent
#assert_no_axioms FX1Poly.Polygraph.icbIsActivePair

-- T2: the six rules
#assert_no_axioms FX1Poly.Polygraph.icbMkGamma
#assert_no_axioms FX1Poly.Polygraph.icbMkDelta
#assert_no_axioms FX1Poly.Polygraph.icbMkEps
#assert_no_axioms FX1Poly.Polygraph.icbInteract

-- T3: reduction, normal forms, diamond
#assert_no_axioms FX1Poly.Polygraph.icbCat
#assert_no_axioms FX1Poly.Polygraph.icbCatWire
#assert_no_axioms FX1Poly.Polygraph.icbExpand
#assert_no_axioms FX1Poly.Polygraph.icbWiringDrop
#assert_no_axioms FX1Poly.Polygraph.icbMaxNat
#assert_no_axioms FX1Poly.Polygraph.icbMaxId
#assert_no_axioms FX1Poly.Polygraph.icbMaxInList
#assert_no_axioms FX1Poly.Polygraph.icbMaxPort
#assert_no_axioms FX1Poly.Polygraph.icbFreshBase
#assert_no_axioms FX1Poly.Polygraph.icbReduceAt
#assert_no_axioms FX1Poly.Polygraph.icbScanFrom
#assert_no_axioms FX1Poly.Polygraph.icbFirstActivePairAux
#assert_no_axioms FX1Poly.Polygraph.icbFirstActivePair
#assert_no_axioms FX1Poly.Polygraph.icbReduceStep
#assert_no_axioms FX1Poly.Polygraph.icbIsNormalForm
#assert_no_axioms FX1Poly.Polygraph.icbDiamondEpsA
#assert_no_axioms FX1Poly.Polygraph.icbDiamondEpsB
#assert_no_axioms FX1Poly.Polygraph.icbDiamondEpsC
#assert_no_axioms FX1Poly.Polygraph.icbDiamondEpsD
#assert_no_axioms FX1Poly.Polygraph.icbDiamondNet
#assert_no_axioms FX1Poly.Polygraph.icbDisjointRedexDiamond

-- T4: walls
#assert_no_axioms FX1Poly.Polygraph.icbHasGlobalTermination
#assert_no_axioms FX1Poly.Polygraph.icbHasFullConfluence

-- T5: fires
#assert_no_axioms FX1Poly.Polygraph.icbFireGammaA
#assert_no_axioms FX1Poly.Polygraph.icbFireGammaB
#assert_no_axioms FX1Poly.Polygraph.icbGammaGammaNet
#assert_no_axioms FX1Poly.Polygraph.icbFireGammaAnnihilates
#assert_no_axioms FX1Poly.Polygraph.icbFireGammaWiring
#assert_no_axioms FX1Poly.Polygraph.icbFireDeltaB
#assert_no_axioms FX1Poly.Polygraph.icbGammaDeltaNet
#assert_no_axioms FX1Poly.Polygraph.icbFireCommuteProducesFour
#assert_no_axioms FX1Poly.Polygraph.icbFireEpsA
#assert_no_axioms FX1Poly.Polygraph.icbFireGammaForErase
#assert_no_axioms FX1Poly.Polygraph.icbEpsGammaNet
#assert_no_axioms FX1Poly.Polygraph.icbFireEraseSpawnsTwo
#assert_no_axioms FX1Poly.Polygraph.icbNormalNet
#assert_no_axioms FX1Poly.Polygraph.icbNormalIsNormal
#assert_no_axioms FX1Poly.Polygraph.icbGammaGammaNotNormal
#assert_no_axioms FX1Poly.Polygraph.icbGammaGammaActive
#assert_no_axioms FX1Poly.Polygraph.icbNormalNotActive
#assert_no_axioms FX1Poly.Polygraph.icbReduceStepFires

end FX1PolyAudit
