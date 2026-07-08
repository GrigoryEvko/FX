import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Computad.MonadSeed

/-! # FX1PolyAudit.Polygraph.Computad.MonadSeed — zero-axiom gate (the walking-monad seed presentation)

Per-declaration zero-axiom gate for the walking-monad seed: the one-mode quiver, the endo-1-generator `t`, its
`t·t` / `t·t·t` composites, the unit / multiplication 2-cell generators, the mode signature, and the freeness
smokes.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.monadGraph
#assert_no_axioms FX1Poly.Polygraph.monadT
#assert_no_axioms FX1Poly.Polygraph.monadTThenT
#assert_no_axioms FX1Poly.Polygraph.monadTThenTThenT
#assert_no_axioms FX1Poly.Polygraph.monadModeSignature
#assert_no_axioms FX1Poly.Polygraph.monadT_length
#assert_no_axioms FX1Poly.Polygraph.monadTThenT_length
#assert_no_axioms FX1Poly.Polygraph.monadTThenTThenT_length

end FX1PolyAudit
