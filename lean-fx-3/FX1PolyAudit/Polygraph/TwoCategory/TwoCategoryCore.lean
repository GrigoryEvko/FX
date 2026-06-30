import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.TwoCategoryCore

/-! # FX1PolyAudit.Polygraph.TwoCategory.TwoCategoryCore — zero-axiom gate (mirror shard)

Zero-axiom audit shard mirroring kernel module `FX1Poly.Polygraph.TwoCategory.TwoCategoryCore`: the generic
strict 2-category interface (`RawTwoCategory`), the locally-discrete realizing instance
(`locallyDiscreteTwoCategory`, all 2-cell laws by proof irrelevance), and the rigidity notion
(`RawTwoCategory.IsRigid` + `rigidTwoCellDecEq` + the `locallyDiscreteTwoCategory_isRigid` witness).

Each declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The strict 2-category interface + the locally-discrete realizing instance
#assert_no_axioms FX1Poly.Tier0.RawTwoCategory
#assert_no_axioms FX1Poly.Tier0.locallyDiscreteTwoCategory

-- The rigid / SProp 2-cell restriction (§3.13)
#assert_no_axioms FX1Poly.Tier0.RawTwoCategory.IsRigid
#assert_no_axioms FX1Poly.Tier0.RawTwoCategory.rigidTwoCellDecEq
#assert_no_axioms FX1Poly.Tier0.locallyDiscreteTwoCategory_isRigid

end FX1PolyAudit
