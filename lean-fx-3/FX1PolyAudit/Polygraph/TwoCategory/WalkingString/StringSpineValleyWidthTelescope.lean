import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringSpineValleyWidthTelescope

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringSpineValleyWidthTelescope — zero-axiom gate
(FC-3 r28, the M2 width telescopes)

Per-declaration zero-axiom gate for the string Piece-I length-determinacy core over the walking ADJOINT-TRIPLE
signature: the two width telescopes (cap block drops the open-wire count by `2` per cap, cup block raises it), the
two length-determinacy corollaries (`capLengthEq` / `cupLengthEq` from equal mid-widths), and the four concrete
truth-probes on a genuine string cap `ε` / cup `η'`.  Every declaration must be free of `propext`, `Quot.sound`,
`Classical`, `sorry`, `native_decide`, `omega`.  The project `#assert_no_axioms` macro is fuel-based; the
independent `#print axioms` lines below are the trusted cross-check. -/

namespace FX1PolyAudit

-- ★ the two width telescopes (colour-blind additive width shift, `∓ 2 · length`)
#assert_no_axioms FX1Poly.Polygraph.stringPureCapBlock_widthTelescope
#assert_no_axioms FX1Poly.Polygraph.stringPureCupBlock_widthTelescope

-- ★ the two length-determinacy corollaries (cancel the telescopes)
#assert_no_axioms FX1Poly.Polygraph.stringCapLength_eq_of_midWidth_eq
#assert_no_axioms FX1Poly.Polygraph.stringCupLength_eq_of_midWidth_eq_of_finalWidth_eq

-- probe data (genuine string cap `ε` / cup `η'` at `tip` + their seeds)
#assert_no_axioms FX1Poly.Polygraph.stringWidthTelescopeProbeCapAtom
#assert_no_axioms FX1Poly.Polygraph.stringWidthTelescopeProbeCupAtom
#assert_no_axioms FX1Poly.Polygraph.stringWidthTelescopeProbeCapSeed
#assert_no_axioms FX1Poly.Polygraph.stringWidthTelescopeProbeCupSeed

-- the four concrete truth-probes (fire the ports end-to-end through `processSpine`)
#assert_no_axioms FX1Poly.Polygraph.stringPureCapBlock_widthTelescope_firesOnCapProbe
#assert_no_axioms FX1Poly.Polygraph.stringPureCupBlock_widthTelescope_firesOnCupProbe
#assert_no_axioms FX1Poly.Polygraph.stringCapLength_eq_of_midWidth_eq_firesOnCapProbe
#assert_no_axioms FX1Poly.Polygraph.stringCupLength_eq_of_midWidth_eq_of_finalWidth_eq_firesOnCupProbe

-- honesty marker
#assert_no_axioms FX1Poly.Polygraph.fxString_hasSpineValleyWidthTelescope

-- independent cross-check (the fuel macro is not trusted alone)
#print axioms FX1Poly.Polygraph.stringPureCapBlock_widthTelescope
#print axioms FX1Poly.Polygraph.stringPureCupBlock_widthTelescope
#print axioms FX1Poly.Polygraph.stringCapLength_eq_of_midWidth_eq
#print axioms FX1Poly.Polygraph.stringCupLength_eq_of_midWidth_eq_of_finalWidth_eq
#print axioms FX1Poly.Polygraph.stringPureCapBlock_widthTelescope_firesOnCapProbe
#print axioms FX1Poly.Polygraph.stringPureCupBlock_widthTelescope_firesOnCupProbe
#print axioms FX1Poly.Polygraph.stringCapLength_eq_of_midWidth_eq_firesOnCapProbe
#print axioms FX1Poly.Polygraph.stringCupLength_eq_of_midWidth_eq_of_finalWidth_eq_firesOnCupProbe
#print axioms FX1Poly.Polygraph.fxString_hasSpineValleyWidthTelescope

end FX1PolyAudit
