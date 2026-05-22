import LeanFX2.Foundation.TermPathLamExcludes
import LeanFX2.Tools.DependencyAudit

/-! Smoke audit: `Foundation/TermPathLamExcludes.lean` zero-axiom log.

Reviewer-facing `#print axioms` plus strict `#assert_no_axioms` gate
confirm the vacuity lemma `Term.pathLam_excludes_closedTy` does not
depend on any axiom.

This lemma is the meta-unblocker for future
`RawStep.par.lift_full_hcomp` / `lift_full_hcompPath` /
`lift_full_transp` work: when `DispatchAtom.<ctor>` restricts the
carrier type to `IsClosedTy`-shape, the β-arm disjuncts of
`hcomp_inv` / `transp_inv` (which force `sidesRaw = RawTerm.pathLam
...`) become vacuous via this lemma — Term.pathLam is the unique
constructor with raw `pathLam` and its return type forces `Ty.path
...`, contradicting `IsClosedTy`. -/

namespace LeanFX2.SmokeTermPathLamExcludes

#assert_no_axioms LeanFX2.Term.pathLam_excludes_closedTy

#print axioms LeanFX2.Term.pathLam_excludes_closedTy

end LeanFX2.SmokeTermPathLamExcludes
