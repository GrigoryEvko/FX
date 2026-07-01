import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.InterchangeFree

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.InterchangeFree — zero-axiom gate (mode-3 floor, interchange-free fragment)

Per-declaration zero-axiom gate for the interchange-free fragment of the `TwoCellStep` 3-polygraph: the generic
subrelation-accessibility descent, the embedding of the fragment into the full system, and the fragment's strong
normalization (carried over from the proven `TwoCellStep` SN).

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- ★ Strong normalization descends to a subrelation (the generic Acc-descent)
#assert_no_axioms FX1Poly.Tier0.accessible_ofSubrelation

-- ★ The interchange-free fragment embeds into the full TwoCellStep 3-polygraph
#assert_no_axioms FX1Poly.Tier0.twoCellStepInterchangeFree_isTwoCellStep

-- ★ The interchange-free fragment is strongly normalizing (termination half of the modulo-interchange route)
#assert_no_axioms FX1Poly.Tier0.twoCellStepInterchangeFree_isStronglyNormalizing

end FX1PolyAudit
