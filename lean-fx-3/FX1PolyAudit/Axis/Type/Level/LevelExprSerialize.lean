import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Type.Level.LevelExprSerialize

/-! # FX1PolyAudit.Axis.Type.Level.LevelExprSerialize

Zero-axiom audit shard mirroring kernel module `FX1Poly.Axis.Type.Level.LevelExprSerialize`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Universe.LevelExpr.nodeCount

#assert_no_axioms FX1Poly.Universe.LevelExpr.encodeOnto

#assert_no_axioms FX1Poly.Universe.LevelExpr.encodePrefix

#assert_no_axioms FX1Poly.Universe.LevelExpr.decodeOnto

#assert_no_axioms FX1Poly.Universe.LevelExpr.decodeOnto_encodeOnto_lsucc

#assert_no_axioms FX1Poly.Universe.LevelExpr.decodeOnto_encodeOnto_lmax

#assert_no_axioms FX1Poly.Universe.LevelExpr.decodeOnto_encodeOnto_limax

#assert_no_axioms FX1Poly.Universe.LevelExpr.decodeOnto_encodeOnto

#assert_no_axioms FX1Poly.Universe.LevelExpr.decodeOnto_nodeCount_encodePrefix

end FX1PolyAudit
