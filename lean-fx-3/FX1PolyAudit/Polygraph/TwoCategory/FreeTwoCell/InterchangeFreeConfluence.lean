import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.InterchangeFreeConfluence

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.InterchangeFreeConfluence — zero-axiom gate (mode-3 floor)

Per-declaration zero-axiom gate for the interchange-free fragment's confluence reduction: the four
star-congruence lifts and the Newman reduction (the fragment is confluent given its — now genuinely
dischargeable — local confluence).

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- ★ The star-congruence toolkit for the interchange-free fragment
#assert_no_axioms FX1Poly.Polygraph.twoCellInterchangeFreeReducesStar_whiskerLeftCongr
#assert_no_axioms FX1Poly.Polygraph.twoCellInterchangeFreeReducesStar_whiskerRightCongr
#assert_no_axioms FX1Poly.Polygraph.twoCellInterchangeFreeReducesStar_vcompCongrLeft
#assert_no_axioms FX1Poly.Polygraph.twoCellInterchangeFreeReducesStar_vcompCongrRight

-- ★ Newman: the fragment is confluent given its (true) local confluence
#assert_no_axioms FX1Poly.Polygraph.twoCellStepInterchangeFree_isConfluent

end FX1PolyAudit
