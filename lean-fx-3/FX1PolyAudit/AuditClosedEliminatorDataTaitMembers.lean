import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Eliminators.Core.ClosedEliminatorDataTaitMembers

/-! # FX1PolyAudit/AuditClosedEliminatorDataTaitMembers
    — zero-axiom gate for the closed-scope eliminator family of the FTGEN-11 reconciliation

The scope-0 forward bridge `dataTaitCandidate.toCanonicalFormsClosed` and the six closed-eliminator arms over
`dataTaitCandidate` — `fst`/`snd` (Σ projections), `optionMatch`/`eitherMatch` (sum matchers), `idJ`/`idStrictRec`
(path / strict identity).  With the four recursors (bool/nat/natRec/list) these complete the FTGEN-11 reconciliation
eliminator set.  Must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.dataTaitCandidate.toCanonicalFormsClosed
#assert_no_axioms FX1Poly.Core.fstDataTaitMember
#assert_no_axioms FX1Poly.Core.sndDataTaitMember
#assert_no_axioms FX1Poly.Core.optionMatchDataTaitMember
#assert_no_axioms FX1Poly.Core.eitherMatchDataTaitMember
#assert_no_axioms FX1Poly.Core.idJDataTaitMember
#assert_no_axioms FX1Poly.Core.idStrictRecDataTaitMember

end FX1PolyAudit
