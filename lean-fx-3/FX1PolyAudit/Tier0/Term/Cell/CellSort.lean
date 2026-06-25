import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Term.Cell.CellSort

/-! # FX1PolyAudit.Tier0.Term.Cell.CellSort

Zero-axiom audit shard mirroring kernel module `FX1Poly.Tier0.Term.Cell.CellSort`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.CellSort

#assert_no_axioms FX1Poly.Core.CellSort.all

#assert_no_axioms FX1Poly.Core.CellSort.toCode

#assert_no_axioms FX1Poly.Core.CellSort.ofCode?

#assert_no_axioms FX1Poly.Core.CellSort.ofCode?_toCode

#assert_no_axioms FX1Poly.Core.CellSort.all_length

end FX1PolyAudit
