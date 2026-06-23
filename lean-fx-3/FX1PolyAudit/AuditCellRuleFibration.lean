import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.CellRuleFibration

/-! # FX1PolyAudit/AuditCellRuleFibration
    — zero-axiom gate for the (∞,ω)-polygraph cell-rule fibration (Tier0 → Core → Typed)

The index-abstract Tier0 substrate (`RuleFibration` + its sound inhabitation characterization), the
`CellSort`/`Generator` instantiation (`Core.CellRuleBundle`, exercised through `fxCellRules`'s type),
and the FX instance that wires the `.type` axis to the TYTAB lookup (`fxCellRules` + the canonical
per-generator smokes).  Must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Tier0 substrate: inhabitation is sound (the one generic theorem).
#assert_no_axioms FX1Poly.Tier0.RuleFibration.inhabits_eq_true_iff

-- The FX instance + its definitional `.type`↔TYTAB identity (covers Core's `CellRuleBundle` abbrev,
-- which is `fxCellRules`'s type).
#assert_no_axioms FX1Poly.Typed.fxCellRules
#assert_no_axioms FX1Poly.Typed.fxCellRules_type_eq_typingRows

-- The canonical-generator smokes — the fibration lookup computes per axis.
#assert_no_axioms FX1Poly.Typed.lam_inhabits_type
#assert_no_axioms FX1Poly.Typed.lam_orthogonal_type
#assert_no_axioms FX1Poly.Typed.app_inhabits_type
#assert_no_axioms FX1Poly.Typed.var_not_inhabits_type
#assert_no_axioms FX1Poly.Typed.lam_no_grade_rows

end FX1PolyAudit
