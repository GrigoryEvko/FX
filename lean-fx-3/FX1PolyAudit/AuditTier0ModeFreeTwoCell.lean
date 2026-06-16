import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Mode.FreeTwoCellModel

/-! # FX1PolyAudit/AuditTier0ModeFreeTwoCell — zero-axiom gate for mode-3's free 2-cell model

Per-declaration zero-axiom gate for `mode-3`'s first deliverable (`FX1Poly/Tier0/Mode/FreeTwoCellModel.lean`):
the FREE 2-CELL TERM MODEL over a `ModeSignature` (`RawTwoCellExpr`, the five-generator indexed inductive of
2-cell expressions between parallel 1-cells), its structural `size` measure, the DERIVED horizontal composition
(`hcomp`, the Godement product), the generator embedding of the adjunction seed's unit / counit, a
non-degenerate `vcomp` composite witness with its size facts, and the honesty markers.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The free 2-cell term model + its measures
#assert_no_axioms FX1Poly.Tier0.RawTwoCellExpr
#assert_no_axioms FX1Poly.Tier0.RawTwoCellExpr.size
#assert_no_axioms FX1Poly.Tier0.RawTwoCellExpr.hcomp

-- Generator embedding + non-degeneracy witnesses
#assert_no_axioms FX1Poly.Tier0.adjunctionUnitTwoCell
#assert_no_axioms FX1Poly.Tier0.adjunctionCounitTwoCell
#assert_no_axioms FX1Poly.Tier0.adjunctionUnitThenId
#assert_no_axioms FX1Poly.Tier0.adjunctionUnitTwoCell_size
#assert_no_axioms FX1Poly.Tier0.adjunctionUnitThenId_size

-- Honesty markers
#assert_no_axioms FX1Poly.Tier0.fxMode_hasConvergentThreeCellSystem
#assert_no_axioms FX1Poly.Tier0.fxMode_hasQuotientTwoCategory

end FX1PolyAudit
