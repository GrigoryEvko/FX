import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Term.Generator.GeneratorPolygraphMap

/-! # FX1PolyAudit.Axis.Term.Generator.GeneratorPolygraphMap

Zero-axiom audit shard mirroring kernel module `FX1Poly.Axis.Term.Generator.GeneratorPolygraphMap`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The explicit Generator-to-polygraph-generator map.  PolygraphGenerator presents each former with its
-- boundary (tag + child arity + child boundary shifts, coherently); toPolygraphGenerator is the presentation
-- map; _injective is faithful (distinct generators present distinctly, via toNat_injective); _boundary/_tag
-- confirm the presented data is binderShifts/toNat (rfl); _recoversGenerator is invertible (fromTag
-- round-trips the presented tag).  Zero-axiom: record literal over toNat/arity/binderShifts; rfl projections;
-- congrArg into toNat_injective.
#assert_no_axioms FX1Poly.Core.Generator.toPolygraphGenerator

#assert_no_axioms FX1Poly.Core.Generator.toPolygraphGenerator_injective

#assert_no_axioms FX1Poly.Core.Generator.toPolygraphGenerator_boundary

#assert_no_axioms FX1Poly.Core.Generator.toPolygraphGenerator_tag

#assert_no_axioms FX1Poly.Core.Generator.toPolygraphGenerator_recoversGenerator

end FX1PolyAudit
