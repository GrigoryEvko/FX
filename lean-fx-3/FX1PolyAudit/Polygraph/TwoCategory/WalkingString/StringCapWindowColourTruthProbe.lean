import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringCapWindowColourTruthProbe

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringCapWindowColourTruthProbe — zero-axiom gate
(FC-3 r24, B1)

Per-declaration zero-axiom gate for the located-prefix colour truth-probe.  Must be free of `propext`,
`Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- B1 — the two concrete located-shaped cap atoms (opposite window colours)
#assert_no_axioms FX1Poly.Polygraph.stringColourProbeCapUpper
#assert_no_axioms FX1Poly.Polygraph.stringColourProbeCapLower

-- B1 — both are pure caps
#assert_no_axioms FX1Poly.Polygraph.stringColourProbe_bothPureCap

-- B1 — the window colours read off P1, and their difference
#assert_no_axioms FX1Poly.Polygraph.stringColourProbeCapUpper_windowColour
#assert_no_axioms FX1Poly.Polygraph.stringColourProbeCapLower_windowColour
#assert_no_axioms FX1Poly.Polygraph.stringColourProbe_windowColoursDiffer

-- B1 — the decisive verdict: the r23-planned discharge instance is FALSE
#assert_no_axioms FX1Poly.Polygraph.stringColourProbe_dischargeInstanceFails

-- B1 — the honesty marker
#assert_no_axioms FX1Poly.Polygraph.fxString_hasCapWindowColourTruthProbe

end FX1PolyAudit
