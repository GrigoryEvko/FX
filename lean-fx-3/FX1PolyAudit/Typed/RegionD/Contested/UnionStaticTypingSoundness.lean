import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Engine.Classifier.UnionStaticTypingSoundness

/-! # FX1PolyAudit.Typed.RegionD.Contested.UnionStaticTypingSoundness — zero-axiom gate (REGION-D contested-module mirror, region-D restructure) -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.hasUnionEliminatorTypingRule_falsePeel
#assert_no_axioms FX1Poly.Typed.hasSomeTypingRule_falseOfUnionReserved
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.reservedHeadUntyped
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.headIsUnionLive
#assert_no_axioms FX1Poly.Typed.hasUnionEliminatorTypingRule_hilbertSpace
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.hilbertSpaceHeadUntyped

end FX1PolyAudit
