import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringConvOfMapEqPort

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringConvOfMapEqPort — zero-axiom gate (FC-9, the port-or-wall round)

Per-declaration zero-axiom gate for the FC-9 `convOfMapEq` port closed MODULO the two named sub-producers: the base
conditional completeness and its two-level lift, the keystone and the full decision (each a composition of the shipped
sharpening with the shipped completeness reduction), the machine-witnessed crux configuration (both mixed cup·cap
windows pinned by the r6 crux, plus the exact two-colour valley already canonical), and the two markers (the shipped
conditional-port marker and the still-paused unconditional-flip marker).
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringConvOfMapEq_ofOracleAndValleyTraceEquiv
#assert_no_axioms FX1Poly.Polygraph.stringConvOfColouredMapEq_ofOracleAndValleyTraceEquiv
#assert_no_axioms FX1Poly.Polygraph.stringSaturatedMatchingCanonicalization_ofOracleAndValleyTraceEquiv
#assert_no_axioms FX1Poly.Polygraph.decidableStringSaturatedConv_ofOracleAndValleyTraceEquiv
#assert_no_axioms FX1Poly.Polygraph.stringMixedLowerWindow_cannotStraighten
#assert_no_axioms FX1Poly.Polygraph.stringMixedUpperWindow_cannotStraighten
#assert_no_axioms FX1Poly.Polygraph.stringTwoColourValleyCruxConfiguration
#assert_no_axioms FX1Poly.Polygraph.fxString_hasConvOfMapEqPortModuloTwoResiduals
#assert_no_axioms FX1Poly.Polygraph.fxString_hasConvOfMapEqPortFlip

end FX1PolyAudit
