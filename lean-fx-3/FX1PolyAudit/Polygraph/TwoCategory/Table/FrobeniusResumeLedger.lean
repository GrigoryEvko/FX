import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Table.FrobeniusResumeLedger

/-! # FX1PolyAudit.Polygraph.TwoCategory.Table.FrobeniusResumeLedger — zero-axiom gate for the FROB-RESUME r1
(#2017) per-brick honest ledger + aggregate verdict.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Table.fxTab_frobResumeR1Complete
#assert_no_axioms FX1Poly.Polygraph.Table.fxTab_frobResumeR1Complete_holds
#assert_no_axioms FX1Poly.Polygraph.Table.fxTab_frobResumeR1Residual
#assert_no_axioms FX1Poly.Polygraph.Table.fxTab_frobResumeR1Residual_isOpen
#assert_no_axioms FX1Poly.Polygraph.Table.fxTab_frobResumeR1_decisionShipped
#assert_no_axioms FX1Poly.Polygraph.Table.fxTab_frobResumeR2Shipped
#assert_no_axioms FX1Poly.Polygraph.Table.fxTab_frobResumeR2Shipped_holds
#assert_no_axioms FX1Poly.Polygraph.Table.fxTab_frobResumeR2_wallsAtSeedMerge
#assert_no_axioms FX1Poly.Polygraph.Table.fxTab_frob2017Complete
#assert_no_axioms FX1Poly.Polygraph.Table.fxTab_frob2017Complete_holds
#assert_no_axioms FX1Poly.Polygraph.Table.fxTab_frob2017_complete_witness

end FX1PolyAudit
