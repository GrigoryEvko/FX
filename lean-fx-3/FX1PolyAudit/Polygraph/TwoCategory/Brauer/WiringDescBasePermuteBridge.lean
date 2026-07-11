import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescBasePermuteBridge

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescBasePermuteBridge — zero-axiom gate (BRAUER r25 GAP β)

Per-declaration zero-axiom gate for the GAP β base-permute bridge: the two swap-map naturality lemmas
(`applyAdjacentSwap_map`, `foldlAdjacentSwap_map`), the fusion (`foldlAdjacentSwapBase_eq_mapPermute`), GAP β itself
(`natListGetAt_foldlAdjacentSwapBase`), and the ingredient marker (`fxBrauer_hasBasePermuteBridge`).

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.applyAdjacentSwap_map
#assert_no_axioms FX1Poly.Polygraph.foldlAdjacentSwap_map
#assert_no_axioms FX1Poly.Polygraph.foldlAdjacentSwapBase_eq_mapPermute
#assert_no_axioms FX1Poly.Polygraph.natListGetAt_foldlAdjacentSwapBase
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasBasePermuteBridge

end FX1PolyAudit
