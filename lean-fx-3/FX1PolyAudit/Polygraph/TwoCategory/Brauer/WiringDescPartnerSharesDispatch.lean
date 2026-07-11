import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescPartnerSharesDispatch

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescPartnerSharesDispatch — zero-axiom gate (BRAUER r29 B2)

Per-declaration zero-axiom gate for the unconditional six-arm dispatch: the full-word width
(`foldOpenWiresWidth_correctedWord`), the unconditional `partnerShares_general` and its read-off consumer
(`partnerIndexOf_reads_arc_unconditional`), the general firings on the monster / adversarial-B hostiles, and the
additive marker `fxBrauer_hasUnconditionalPartnerShares` (the wall's content discharged; the frozen boolean kept).

Independent `#print axioms` (in a scratch during development) reported every decl as "does not depend on any axioms".
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in `AuditAll`. -/

namespace FX1PolyAudit

-- Section 1: the full-word open-wire width
#assert_no_axioms FX1Poly.Polygraph.foldOpenWiresWidth_correctedWord

-- Section 2/3: the unconditional dispatch + read-off
#assert_no_axioms FX1Poly.Polygraph.partnerShares_general
#assert_no_axioms FX1Poly.Polygraph.partnerIndexOf_reads_arc_unconditional

-- Section 4: the general firings on the recon hostiles
#assert_no_axioms FX1Poly.Polygraph.partnerShares_firesMonster_zero
#assert_no_axioms FX1Poly.Polygraph.partnerShares_firesMonster_four
#assert_no_axioms FX1Poly.Polygraph.partnerShares_firesMonster_eight
#assert_no_axioms FX1Poly.Polygraph.partnerShares_firesAdversarialB
#assert_no_axioms FX1Poly.Polygraph.partnerIndexOf_readsArc_unconditional_monster_zero

-- Section 5: the additive flip marker
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasUnconditionalPartnerShares

end FX1PolyAudit
