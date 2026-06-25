import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Rewriting.Word.RawCellWordEncoding

/-! # FX1PolyAudit.Core.Rewriting.Word.RawCellWordEncoding

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Rewriting.Word.RawCellWordEncoding`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The dim-1 free-monoid rule-word encoding of the RawCell composite layer, the start of the FX-Conv-to-word
-- bridge.  encodeRuleWord reads off the ordered generating-cell rule ids (the dim-1 rewrite-rule alphabet,
-- distinct from the term-formers): objects/identities to the empty word, generatingCell to [ruleId],
-- composites to ++.  The per-constructor rules are rfl; _assoc + _identity_left/_right are the monoid
-- homomorphism onto the free monoid (List ++ / [] with assoc + two-sided unit); length_eq_generatingCellCount
-- is faithfulness to the rewrite content.  Zero-axiom: structural recursion + local propext-free list/Nat lemmas.
#assert_no_axioms FX1Poly.Core.RawCell.encodeRuleWord

#assert_no_axioms FX1Poly.Core.encodeRuleWord_termBase

#assert_no_axioms FX1Poly.Core.encodeRuleWord_generatingCell

#assert_no_axioms FX1Poly.Core.encodeRuleWord_verticalComposite

#assert_no_axioms FX1Poly.Core.encodeRuleWord_horizontalComposite

#assert_no_axioms FX1Poly.Core.encodeRuleWord_identityCell

#assert_no_axioms FX1Poly.Core.encodeRuleWord_assoc

#assert_no_axioms FX1Poly.Core.encodeRuleWord_identity_left

#assert_no_axioms FX1Poly.Core.encodeRuleWord_identity_right

#assert_no_axioms FX1Poly.Core.RawCell.generatingCellCount

#assert_no_axioms FX1Poly.Core.encodeRuleWord_length_eq_generatingCellCount

end FX1PolyAudit
