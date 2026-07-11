import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringWidthZeroCupSortBaseCase

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringWidthZeroCupSortBaseCase — zero-axiom gate
(FC-3 r13, B3 down-payment)

Per-declaration zero-axiom gate for the width-0 pure-cup sort's singleton base case
(`stringWidthZeroPureCupShared_singleton`) and the marker.  The private `Nat`-sum helper is covered transitively.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringWidthZeroPureCupShared_singleton
#assert_no_axioms FX1Poly.Polygraph.fxString_hasWidthZeroCupSortBaseCase

end FX1PolyAudit
