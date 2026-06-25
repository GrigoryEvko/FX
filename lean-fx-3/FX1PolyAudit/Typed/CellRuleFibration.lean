import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.CellRuleFibration

/-! # FX1PolyAudit.Typed.CellRuleFibration

Zero-axiom audit shard mirroring kernel module `FX1Poly.Typed.CellRuleFibration`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

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
