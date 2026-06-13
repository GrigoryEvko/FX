import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.TableOneStepReducts

/-! # FX1PolyAudit/AuditTableOneStepReducts — IOTA-T9 enumeration shard

Per-declaration zero-axiom gate for the exact table reduct enumeration:
the forward membership helpers, the mutual enumeration, soundness, and
★ completeness over well-formed tables (the half the bespoke
enumeration deferred).  The canonical 21-row instantiation is
`RawTerm.oneStepReducts` (gated in `AuditTypedSubstVecCwR`).  Every
declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

/-! ## Forward membership helpers -/

#assert_no_axioms FX1Poly.Core.listMemAppendRight
#assert_no_axioms FX1Poly.Core.listMemMapForward

/-! ## The enumeration -/

#assert_no_axioms FX1Poly.Core.oneStepReductsOverTable
#assert_no_axioms FX1Poly.Core.oneStepChildrenReductsOverTable

/-! ## Soundness -/

#assert_no_axioms FX1Poly.Core.oneStepReductsOverTable_sound
#assert_no_axioms FX1Poly.Core.oneStepChildrenReductsOverTable_sound

/-! ## ★ Completeness -/

#assert_no_axioms FX1Poly.Core.oneStepReductsOverTable_complete
#assert_no_axioms FX1Poly.Core.oneStepChildrenReductsOverTable_complete

end FX1PolyAudit
