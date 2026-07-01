import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.Confluence

/-! # FX1PolyAudit.Tier0.Mode.FreeTwoCellConfluence — zero-axiom gate (mode-3 floor, confluence reduction)

Per-declaration zero-axiom gate for the confluence reduction of the `TwoCellStep` 3-polygraph: the four
star-congruence lifts (a many-step reduction lifts through each one-hole context) and the Newman reduction
(`TwoCellStep` is confluent GIVEN local confluence, via the proven strong-normalization floor).

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- ★ The star-congruence toolkit (a many-step reduction lifts through each one-hole context)
#assert_no_axioms FX1Poly.Tier0.twoCellReducesStar_whiskerLeftCongr
#assert_no_axioms FX1Poly.Tier0.twoCellReducesStar_whiskerRightCongr
#assert_no_axioms FX1Poly.Tier0.twoCellReducesStar_vcompCongrLeft
#assert_no_axioms FX1Poly.Tier0.twoCellReducesStar_vcompCongrRight

-- ★ Newman: TwoCellStep is confluent given local confluence (convergence reduced to the one obligation)
#assert_no_axioms FX1Poly.Tier0.twoCellStep_isConfluent

end FX1PolyAudit
