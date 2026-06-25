import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Engine.RuleTables.TypingRoleOrthogonality

/-! # FX1PolyAudit/AuditTypingRoleOrthogonality
    — zero-axiom gate for TYTAB-1 brick 2.5: the static-side `WfIotaTable`

The role-class orthogonality certificate over the unified typing-table bundle: every generator is a
type-former XOR a constructor XOR an eliminator (`roleClassesAreOrthogonal`, full-enumeration), the
sole within-formation-class duplicate `gen_unitCode` characterized honestly, per-table uniqueness
away from it (the arm-rebasing precondition), and the unique-row `Option` view with its canonical
computations. -/

#assert_no_axioms FX1Poly.Typed.firesFormationRole
#assert_no_axioms FX1Poly.Typed.firesIntroRole
#assert_no_axioms FX1Poly.Typed.firesElimRole
#assert_no_axioms FX1Poly.Typed.firesAtMostOneRoleClass

#assert_no_axioms FX1Poly.Typed.fxTypingRolesWellFormed
#assert_no_axioms FX1Poly.Typed.typingRoleClassesOrthogonal

#assert_no_axioms FX1Poly.Typed.unitCode_overlapsWithinFormationClassOnly
#assert_no_axioms FX1Poly.Typed.unitCode_firesTwoFormationRows

#assert_no_axioms FX1Poly.Typed.firesAtMostOneRow
#assert_no_axioms FX1Poly.Typed.typingRowsAreUnique_of_ne_unitCode

#assert_no_axioms FX1Poly.Typed.typingRowOf
#assert_no_axioms FX1Poly.Typed.typingRowOf_lam
#assert_no_axioms FX1Poly.Typed.typingRowOf_app
#assert_no_axioms FX1Poly.Typed.typingRowOf_piTyCode
#assert_no_axioms FX1Poly.Typed.typingRowOf_var_none

#assert_no_axioms FX1Poly.Typed.lam_isIntroClassOnly
#assert_no_axioms FX1Poly.Typed.app_isElimClassOnly
#assert_no_axioms FX1Poly.Typed.piTyCode_isFormationClassOnly
