import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Term.Generator.GeneratorCountPin

/-! # FX1PolyAudit.Axis.Term.Generator.GeneratorCountPinCoreCellsAudit

Zero-axiom audit shard mirroring kernel module `FX1Poly.Axis.Term.Generator.GeneratorCountPin`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- GENERATOR-COUNT PIN (permanent stale-count guard): the enum has exactly 205 constructors —
-- gen_npComplete attains index 202 (count from below) and every index is < 203 (count from above,
-- the theorem a 204th generator breaks).  Update generatorCount + count-citing docstrings together.
#assert_no_axioms FX1Poly.Core.generatorCount_lastIndex

#assert_no_axioms FX1Poly.Core.generatorCount_upperBound

end FX1PolyAudit
