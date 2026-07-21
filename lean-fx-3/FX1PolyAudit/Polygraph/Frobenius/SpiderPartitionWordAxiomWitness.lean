import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Frobenius.SpiderPartitionWord

/-! # FX1PolyAudit.Polygraph.Frobenius.SpiderPartitionWordAxiomWitness — zero-axiom gate

Per-declaration `#assert_no_axioms` gate over every headline of the standalone spider-theorem
build (`FX1Poly.Polygraph.SpiderPartition`): the cons-only primitives, the fuel union-find, the
canonicaliser, the FrobDiagram carrier + constructor, the spider generators, composition, the
decision metatheory (soundness / completeness / refutation / decidability), the FrobConv congruence
+ its nine constructors, the three walls, and the ground fires.  Parity is EXACT with the shipped
file: one directive per shipped declaration (inductives + every constructor). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.fspListGet
#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.fspListBeq
#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.fspNatBeqRefl
#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.fspNatBeqEq
#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.fspAndElim
#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.fspListBeqRefl
#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.fspListBeqEq
#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.fspParent
#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.fspRoot
#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.fspRootOf
#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.fspJoin
#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.fspJoinVec
#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.fspLeastRep
#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.fspRepVecOver
#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.fspCanonicalise
#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.fspVecCanonicalFrom
#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.fspVecCanonical
#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.FspFrobDiagram
#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.FspFrobDiagram.mk
#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.fspDecideEq
#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.fspWellFormed
#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.fspZeros
#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.fspCountUp
#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.fspAppendNat
#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.fspSpider
#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.fspIdentityVec
#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.fspIdentity
#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.fspUnit
#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.fspCounit
#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.fspMult
#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.fspComult
#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.fspSwap
#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.fspOuterToUniverse
#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.fspOuterLeastRep
#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.fspOuterRepVec
#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.fspCompose
#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.fspDecideEqRefl
#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.fspDecideEqEq
#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.fspDecideEqSymm
#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.fspDecideEqTrans
#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.FspFrobConv
#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.FspFrobConv.refl
#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.FspFrobConv.symm
#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.FspFrobConv.trans
#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.FspFrobConv.spiderFusion
#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.FspFrobConv.multCounit
#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.FspFrobConv.unitComult
#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.FspFrobConv.unitCounit
#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.FspFrobConv.identityLeftMult
#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.FspFrobConv.identityLeftId
#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.fspFrobConv_partitionSound
#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.fspFrobConv_complete
#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.fspFrobConv_refute
#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.fspFrobConv_iff_decide
#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.instFspFrobConvDecidable
#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.fspHasNonSpecialCircleCount
#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.fspHasPlanarCyclicOrder
#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.fspHasInteractingBialgebraCompleteness
#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.fspFire_spiderFusion
#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.fspFire_unitCounitRound
#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.fspFire_swapNotIdentity
#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.fspFire_identityLeftMult
#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.fspFire_identityLeftId
#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.fspFire_canonicaliseIdempotentZeros
#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.fspFire_canonicaliseIdempotentId
#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.fspFire_multWellFormed
#assert_no_axioms FX1Poly.Polygraph.SpiderPartition.fspFire_identityWellFormed

end FX1PolyAudit
