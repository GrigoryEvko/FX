import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadDescentInterfaceLedger

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingMonad.MonadDescentInterfaceLedger — zero-axiom gate

Per-declaration zero-axiom gate for the descent-interface ledger recording what the closed walking-monad word
problem delivers to the #2043 JAM-A gate (downstream discharged, mode-side residual surviving).  Must be free of
`propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.fxMonad_wpDischargesPerGapDescentDownstream
#assert_no_axioms FX1Poly.Polygraph.fxMonad_wpClosesJamAGate
#assert_no_axioms FX1Poly.Polygraph.reconWpMonad_perGapDescentDownstreamClosed

end FX1PolyAudit
