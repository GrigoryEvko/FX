import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Table.WalkerDualityInstances

/-! # FX1PolyAudit.Polygraph.TwoCategory.Table.WalkerDualityInstances — zero-axiom gate for the three decided
DUAL walkers (comonad, idempotent comonad, co-KZ) (WALKER-DUALITY B3).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Table.comonadModeSignature
#assert_no_axioms FX1Poly.Polygraph.Table.ComonadLawRel
#assert_no_axioms FX1Poly.Polygraph.Table.decideSaturatedConvOverComonadNative
#assert_no_axioms FX1Poly.Polygraph.Table.comonadDecidesTrue_coassoc
#assert_no_axioms FX1Poly.Polygraph.Table.comonadDecidesTrue_coassoc_holds
#assert_no_axioms FX1Poly.Polygraph.Table.comonadDecidesFalse_faces
#assert_no_axioms FX1Poly.Polygraph.Table.comonadDecidesFalse_faces_holds
#assert_no_axioms FX1Poly.Polygraph.Table.idempotentComonadModeSignature
#assert_no_axioms FX1Poly.Polygraph.Table.IdempotentComonadLawRel
#assert_no_axioms FX1Poly.Polygraph.Table.decideSaturatedConvOverIdempotentComonadNative
#assert_no_axioms FX1Poly.Polygraph.Table.idempotentComonadDecidesTrue_coassoc
#assert_no_axioms FX1Poly.Polygraph.Table.idempotentComonadDecidesTrue_coassoc_holds
#assert_no_axioms FX1Poly.Polygraph.Table.coKZTwoCellLE
#assert_no_axioms FX1Poly.Polygraph.Table.decideCoKZLETotal
#assert_no_axioms FX1Poly.Polygraph.Table.coKZDecidesTrue_reversed
#assert_no_axioms FX1Poly.Polygraph.Table.coKZDecidesTrue_reversed_holds
#assert_no_axioms FX1Poly.Polygraph.Table.coKZDecidesFalse_forward
#assert_no_axioms FX1Poly.Polygraph.Table.coKZDecidesFalse_forward_holds
#assert_no_axioms FX1Poly.Polygraph.Table.fxTab_hasWalkerDualityInstances

end FX1PolyAudit
