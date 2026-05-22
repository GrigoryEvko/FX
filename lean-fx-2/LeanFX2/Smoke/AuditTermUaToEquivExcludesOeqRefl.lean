import LeanFX2.Foundation.TermUaToEquivExcludesOeqRefl
import LeanFX2.Tools.DependencyAudit

/-! Smoke audit: `Foundation/TermUaToEquivExcludesOeqRefl.lean`
zero-axiom log.

Reviewer-facing `#print axioms` plus strict `#assert_no_axioms` gate
confirm the vacuity lemma `Term.uaToEquiv_excludes_oeqRefl_witness`
and its helper `Term.oeqRefl_raw_inv` do not depend on any axiom.

This lemma is the meta-unblocker for future
`RawStep.par.lift_full_equivApply` work (Family E close-out task
#2059, unblock-A.leaf.equivApply #2013): the β arms of
`RawStep.par.equivApply_inv` (`uaReflEquivApply` /
`uaReflEquivApplyDeep`) reduce a typed `Term.equivApply equivTerm
argumentTerm` whose `equivTerm` would need raw projection
`RawTerm.uaToEquiv (RawTerm.oeqRefl _)` — impossible at the typed
level because `Term.uaToEquiv.proof` requires `Ty.id ...` while
`Term.oeqRefl` produces `Ty.oeq ...`.

Same recipe as `Term.pathLam_excludes_closedTy` (commit 92fa8c42)
which unblocked the closed-carrier case of `lift_full_hcomp` (#2066,
commit cf43720b). -/

namespace LeanFX2.SmokeTermUaToEquivExcludesOeqRefl

#assert_no_axioms LeanFX2.Term.uaToEquiv_excludes_oeqRefl_witness
#assert_no_axioms LeanFX2.Term.oeqRefl_raw_inv

#print axioms LeanFX2.Term.uaToEquiv_excludes_oeqRefl_witness
#print axioms LeanFX2.Term.oeqRefl_raw_inv

end LeanFX2.SmokeTermUaToEquivExcludesOeqRefl
