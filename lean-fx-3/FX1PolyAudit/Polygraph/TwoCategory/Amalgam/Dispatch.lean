import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.Dispatch

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.Dispatch — zero-axiom gate for the dispatch statement

Per-declaration zero-axiom gate for the categorical Nelson-Oppen dispatch STATEMENT (the AMALG-2 target): the
disjoint-generator predicate (`wordBelow` / `wordAtOrAbove` / `generatorIsComponentPure` /
`computadGeneratorsDisjoint`), the `DispatchDecidability` structure, and the honest `fxAmalg_hasDispatchTheorem`
marker.  The dispatch THEOREM (inhabiting the structure's arrow) is deferred to WP-AMALG-2 and is NOT gated here.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.wordBelow
#assert_no_axioms FX1Poly.Polygraph.Amalgam.wordAtOrAbove
#assert_no_axioms FX1Poly.Polygraph.Amalgam.generatorIsComponentPure
#assert_no_axioms FX1Poly.Polygraph.Amalgam.computadGeneratorsDisjoint
#assert_no_axioms FX1Poly.Polygraph.Amalgam.DispatchDecidability
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasDispatchTheorem

end FX1PolyAudit
