import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.InterchangeFreeConfluence

/-! # FX1PolyAudit.Tier0.Mode.FreeTwoCellInterchangeFreeConfluence — zero-axiom gate (mode-3 floor)

Per-declaration zero-axiom gate for the interchange-free fragment's confluence reduction: the four
star-congruence lifts and the Newman reduction (the fragment is confluent given its — now genuinely
dischargeable — local confluence).

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- ★ The star-congruence toolkit for the interchange-free fragment
#assert_no_axioms FX1Poly.Tier0.twoCellInterchangeFreeReducesStar_whiskerLeftCongr
#assert_no_axioms FX1Poly.Tier0.twoCellInterchangeFreeReducesStar_whiskerRightCongr
#assert_no_axioms FX1Poly.Tier0.twoCellInterchangeFreeReducesStar_vcompCongrLeft
#assert_no_axioms FX1Poly.Tier0.twoCellInterchangeFreeReducesStar_vcompCongrRight

-- ★ Newman: the fragment is confluent given its (true) local confluence
#assert_no_axioms FX1Poly.Tier0.twoCellStepInterchangeFree_isConfluent

end FX1PolyAudit
