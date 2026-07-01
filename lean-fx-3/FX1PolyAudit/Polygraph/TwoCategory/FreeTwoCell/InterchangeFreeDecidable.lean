import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.InterchangeFreeDecidable

/-! # FX1PolyAudit.Tier0.Mode.FreeTwoCellInterchangeFreeDecidable — zero-axiom gate (mode-3 floor)

Per-declaration zero-axiom gate for the DECISION of interchange-free 2-cell convertibility — the convergent
normalizer composed with decidable syntactic equality of free 2-cell expressions.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Tier0.decidableInterchangeFreeConv

end FX1PolyAudit
