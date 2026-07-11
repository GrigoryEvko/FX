import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringWidthZeroForcingAdjudication

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringWidthZeroForcingAdjudication — zero-axiom gate (FC-3 r12, B1)

Per-declaration zero-axiom gate for the width-0 pure-cup determinacy FORCE adjudication: the endpoint-mode cup-cod
forcing (`stringBaseCup_codForced`, `stringTipCup_codForced`), the `H·G` / `G·F` candidate refutations
(`stringNoCupHasCodHG`, `stringNoCupHasCodGF`), and the marker.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringBaseCup_codForced
#assert_no_axioms FX1Poly.Polygraph.stringTipCup_codForced
#assert_no_axioms FX1Poly.Polygraph.stringNoCupHasCodHG
#assert_no_axioms FX1Poly.Polygraph.stringNoCupHasCodGF
#assert_no_axioms FX1Poly.Polygraph.fxString_widthZeroPureCupDeterminacy_isForced

end FX1PolyAudit
