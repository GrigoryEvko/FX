import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.Validity.HasTypeUnionElimConservativity

/-! # FX1PolyAudit/AuditHasTypeUnionElimConservativity — TYTAB-2 CONS audit shard

Per-declaration zero-axiom gate for the conservativity of the Route-A elim-formedness hardening: the six
branch-selecting row arms, the two projection arms + pathApp, the codomain-strengthening residual + the
eitherMatch arm modulo it, and the coverage record / witness.  Every declaration below must be free of
`propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

/-! ## The six branch-selecting row arms -/

#assert_no_axioms FX1Poly.Typed.boolElimConservative
#assert_no_axioms FX1Poly.Typed.natElimConservative
#assert_no_axioms FX1Poly.Typed.natRecConservative
#assert_no_axioms FX1Poly.Typed.optionMatchConservative
#assert_no_axioms FX1Poly.Typed.idJConservative
#assert_no_axioms FX1Poly.Typed.listElimConservative

/-! ## The two projection arms + pathApp (output recovered from the scrutinee's data code) -/

#assert_no_axioms FX1Poly.Typed.fstConservative
#assert_no_axioms FX1Poly.Typed.sndConservative
#assert_no_axioms FX1Poly.Typed.pathAppConservative

/-! ## The codomain-strengthening residual + the eitherMatch arm modulo it -/

#assert_no_axioms FX1Poly.Typed.CodomainStrengthens
#assert_no_axioms FX1Poly.Typed.eitherMatchConservativeOfStrengthening

/-! ## Coverage record + witness -/

#assert_no_axioms FX1Poly.Typed.ElimHardeningConservativeCoverage
#assert_no_axioms FX1Poly.Typed.elimHardeningConservativeCoverageWitness

end FX1PolyAudit
