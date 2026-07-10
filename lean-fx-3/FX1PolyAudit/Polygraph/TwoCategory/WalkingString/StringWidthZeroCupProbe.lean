import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringWidthZeroCupProbe

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringWidthZeroCupProbe — zero-axiom gate (FC-3 r10, B1)

Per-declaration zero-axiom gate for the width-0 pure-cup determinacy truth-probe on the hand-worked disjoint-cup pair
(`stringWidthZeroPureCupDeterminacy_probe`) and its marker.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringWidthZeroPureCupDeterminacy_probe
#assert_no_axioms FX1Poly.Polygraph.fxString_hasWidthZeroCupDeterminacyProbe

end FX1PolyAudit
