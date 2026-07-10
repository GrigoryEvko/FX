import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Rewriting.SemiThueReduction

/-! # FX1PolyAudit/Polygraph/Rewriting/SemiThueReduction — zero-axiom gate (WP-CEIL-UNDEC Burroni bridge)

Per-declaration zero-axiom gate for the mechanized semi-Thue ⟷ one-object-2-polygraph reduction: the clean
local list-append helpers, the semi-Thue system + Thue congruence + whisker congruences, the one-object
2-polygraph carrier (`encodedGraph` / `encodeWord` / `decodeWord` + the homs), the encoded 2-cell
convertibility + the `ModeSignature` faithfulness landing, BOTH reduction directions + the iff, the involution
non-vacuity instance + its parity separation, and the marker + its bridge pin.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

-- Clean list-append helpers (core append_assoc / append_nil leak propext)
#assert_no_axioms FX1Poly.Polygraph.appendNilClean
#assert_no_axioms FX1Poly.Polygraph.appendAssocClean

-- The semi-Thue system + Thue congruence + whisker congruences
#assert_no_axioms FX1Poly.Polygraph.SemiThueStep
#assert_no_axioms FX1Poly.Polygraph.ThueCong
#assert_no_axioms FX1Poly.Polygraph.thueCong_of_mem
#assert_no_axioms FX1Poly.Polygraph.whiskerLeftReassoc
#assert_no_axioms FX1Poly.Polygraph.whiskerRightReassoc
#assert_no_axioms FX1Poly.Polygraph.semiThueStep_whiskerLeft
#assert_no_axioms FX1Poly.Polygraph.semiThueStep_whiskerRight
#assert_no_axioms FX1Poly.Polygraph.thueCong_whiskerLeft
#assert_no_axioms FX1Poly.Polygraph.thueCong_whiskerRight

-- The one-object 2-polygraph carrier + the monoid-iso homs
#assert_no_axioms FX1Poly.Polygraph.EncodedMode
#assert_no_axioms FX1Poly.Polygraph.encodedGraph
#assert_no_axioms FX1Poly.Polygraph.encodeWord
#assert_no_axioms FX1Poly.Polygraph.decodeWord
#assert_no_axioms FX1Poly.Polygraph.decode_encode
#assert_no_axioms FX1Poly.Polygraph.encodeWord_append
#assert_no_axioms FX1Poly.Polygraph.encodeWord_sandwich
#assert_no_axioms FX1Poly.Polygraph.decodeWord_nil
#assert_no_axioms FX1Poly.Polygraph.decodeWord_cons
#assert_no_axioms FX1Poly.Polygraph.decodeWord_compose_ofLength
#assert_no_axioms FX1Poly.Polygraph.decodeWord_compose

-- The encoded 2-cell convertibility + the ModeSignature faithfulness landing
#assert_no_axioms FX1Poly.Polygraph.EncodedConv
#assert_no_axioms FX1Poly.Polygraph.encodedRuleTwoCell
#assert_no_axioms FX1Poly.Polygraph.encodedModeSignature
#assert_no_axioms FX1Poly.Polygraph.ruleGivesTwoCell
#assert_no_axioms FX1Poly.Polygraph.twoCellGivesRule

-- The reduction — both directions + the iff
#assert_no_axioms FX1Poly.Polygraph.thue_to_encoded
#assert_no_axioms FX1Poly.Polygraph.encoded_to_thue
#assert_no_axioms FX1Poly.Polygraph.semiThue_iff_encodedTwoCell

-- Non-vacuity — the involution 1-rule instance + its parity separation
#assert_no_axioms FX1Poly.Polygraph.InvolutionLetter
#assert_no_axioms FX1Poly.Polygraph.involutionThueRules
#assert_no_axioms FX1Poly.Polygraph.involutionThueRule_mem
#assert_no_axioms FX1Poly.Polygraph.involutionThue_positive
#assert_no_axioms FX1Poly.Polygraph.involutionThue_reductionInstance
#assert_no_axioms FX1Poly.Polygraph.involutionWordParity
#assert_no_axioms FX1Poly.Polygraph.boolNotXor
#assert_no_axioms FX1Poly.Polygraph.xorFalseLeft
#assert_no_axioms FX1Poly.Polygraph.involutionWordParity_append
#assert_no_axioms FX1Poly.Polygraph.involutionRuleParityBalanced
#assert_no_axioms FX1Poly.Polygraph.involutionThue_preservesParity
#assert_no_axioms FX1Poly.Polygraph.involutionThue_separation

-- The marker + its bridge pin
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasSemiThueReductionMechanized
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasSemiThueReductionMechanized_isBridge

end FX1PolyAudit
