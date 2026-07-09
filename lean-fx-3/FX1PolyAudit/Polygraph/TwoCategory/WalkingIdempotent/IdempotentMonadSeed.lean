import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingIdempotent.IdempotentMonadSeed

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingIdempotent.IdempotentMonadSeed — zero-axiom gate (the two idempotence faces)

Per-declaration zero-axiom gate for the walking-idempotent-monad seed: the two idempotence face cells
`eta ▷ t` / `t ◁ eta` and their size / distinctness smokes.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.monadEtaTCell
#assert_no_axioms FX1Poly.Polygraph.monadTEtaCell
#assert_no_axioms FX1Poly.Polygraph.monadEtaTCell_size
#assert_no_axioms FX1Poly.Polygraph.monadTEtaCell_size
#assert_no_axioms FX1Poly.Polygraph.monadEtaTCell_ne_monadTEtaCell_headWhisker

end FX1PolyAudit
