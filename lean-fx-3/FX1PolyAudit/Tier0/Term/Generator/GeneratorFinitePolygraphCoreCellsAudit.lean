import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Term.Generator.GeneratorFinitePolygraph

/-! # FX1PolyAudit.Tier0.Term.Generator.GeneratorFinitePolygraphCoreCellsAudit

Zero-axiom audit shard mirroring kernel module `FX1Poly.Tier0.Term.Generator.GeneratorFinitePolygraph`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The FX kernel as a finite polygraph over the 203-Generator table.  The generators are indexed injectively
-- (toNat_injective) and boundedly (toNat_lt) into Fin 203, with the total inverse table fromTag (round-trip
-- fromTag_toNat + range-totality fromTag_total_on_range); each carries its dimension (arity) and boundary
-- (binderShifts), coherently (binderShifts_length_eq_arity).  fxKernelPolygraph bundles all of it.  Zero-axiom
-- via cases + bounded decide with raised maxRecDepth (plain decide, not native_decide).
#assert_no_axioms FX1Poly.Core.Generator.toNat_lt

#assert_no_axioms FX1Poly.Core.Generator.fromTag_total_on_range

#assert_no_axioms FX1Poly.Core.fxKernelPolygraph

end FX1PolyAudit
