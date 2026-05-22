import LeanFX2.Foundation.TermTranspPathVacuity
import LeanFX2.Tools.DependencyAudit

/-! Smoke audit: `Foundation/TermTranspPathVacuity.lean` zero-axiom log.

Reviewer-facing `#print axioms` plus strict `#assert_no_axioms` gates
confirm the two transp-leaf vacuity lemmas do not depend on any
axiom.

These lemmas are the meta-unblocker for the future
`RawStep.par.lift_full_transp` leaf (#2065 unblock-E.transp.Close):
4 of the 7 raw inversion arms of `RawStep.par.transp_inv` (uaBeta,
uaBetaDeep, transpCompose, transpComposeDeep) discharge via these
vacuity refutations, because the typed `Term.transp` pathSource at
`Ty.path ...` cannot have raw projection `RawTerm.uaToEquiv _` or
`RawTerm.pathCompose _ _`.

Same recipe as `Term.pathLam_excludes_closedTy`
(`Foundation/TermPathLamExcludes.lean`, #2066) and
`Term.uaToEquiv_excludes_oeqRefl_witness`
(`Foundation/TermUaToEquivExcludesOeqRefl.lean`, #2057). -/

namespace LeanFX2.SmokeTermTranspPathVacuity

#assert_no_axioms LeanFX2.Term.uaToEquiv_excludes_pathTy
#assert_no_axioms LeanFX2.Term.pathCompose_uninhabited

#print axioms LeanFX2.Term.uaToEquiv_excludes_pathTy
#print axioms LeanFX2.Term.pathCompose_uninhabited

end LeanFX2.SmokeTermTranspPathVacuity
