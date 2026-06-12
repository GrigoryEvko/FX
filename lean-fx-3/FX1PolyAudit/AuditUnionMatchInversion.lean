import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.HasTypeUnionMatchInversion

/-! # FX1PolyAudit/AuditUnionMatchInversion — per-head match inversions for the union judgment

Per-declaration zero-axiom gate for the three two-branch-match per-head inversions on `HasTypeUnion`
(boolElim / optionMatch / eitherMatch): free-subject `cases` + the shipped row inverter
`nativeTwoBranchMatchRuleOf_cases` + head-generator no-confusion + child drilling.  This shard was
promised by the source file's docstring but had not shipped — the three theorems were previously
ungated.  Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.HasTypeUnion.invertAtBoolElimHead
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.invertAtOptionMatchHead
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.invertAtEitherMatchHead

end FX1PolyAudit
