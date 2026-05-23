import LeanFX2.Reduction.Eta
import LeanFX2.Tools.DependencyAudit

/-! # AuditEta — zero-axiom audit for `Step.eta` (accelerate-P0.1).

Smoke gates for the keystone η-reduction kernel shipped in
`LeanFX2.Reduction.Eta`.  Verifies that the new sibling inductive
`Step.eta` and its two arrow / path constructors are axiom-clean
and concretely constructible on a minimal witness.

## Coverage

* `Step.eta` — the inductive itself (kernel-level).
* `Step.eta.etaLam`  — non-dep arrow η rule.
* `Step.eta.etaPath` — cubical path η rule (univalent mode).
* `Step.eta.demoEtaLam_constructible` — concrete witness that the
  arrow rule produces a step on a freely-chosen function term.
* `Step.eta.demoEtaPath_constructible` — concrete witness for the
  path rule on a freely-chosen path term in univalent mode.

## Strength-T12-binder dependency (shipped)

Both witness theorems consume
`Term.eta_lam_shape_construct` and `Term.eta_path_shape_construct`
from the `strength-T12-binder` foundation (#1968).  Their own
audit gate lives in `Smoke/AuditTermWeakenInverse.lean`.
-/

namespace LeanFX2.SmokeEta

open LeanFX2

/-- The η-arrow rule fires on every function term: from any
`functionTerm : Term context (Ty.arrow domain codomain) functionRaw`,
we get `Step.eta (lam (f.weaken `app` var 0)) functionTerm`.  This
demonstrates the rule is non-vacuous and the LHS / RHS Ty indices
align under the two-Ty `Step.eta` signature. -/
theorem demoEtaLam_constructible
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {functionRaw : RawTerm scope}
    (functionTerm :
      Term context (Ty.arrow domainType codomainType) functionRaw) :
    Step.eta
      (Term.lam (codomainType := codomainType)
        (Term.eta_lam_shape_construct functionTerm))
      functionTerm :=
  Step.eta.etaLam functionTerm

/-- The η-path rule fires on every path term in univalent mode. -/
theorem demoEtaPath_constructible
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint pathRaw : RawTerm scope}
    (pathTerm :
      Term context (Ty.path carrierType leftEndpoint rightEndpoint)
        pathRaw) :
    Step.eta
      (Term.pathLam
        (mode := mode) (context := context)
        modeIsUnivalent carrierType leftEndpoint rightEndpoint
        (Term.eta_path_shape_construct modeIsUnivalent pathTerm))
      pathTerm :=
  Step.eta.etaPath modeIsUnivalent pathTerm

#assert_no_axioms LeanFX2.SmokeEta.demoEtaLam_constructible
#assert_no_axioms LeanFX2.SmokeEta.demoEtaPath_constructible

#print axioms LeanFX2.Step.eta
#print axioms LeanFX2.Step.eta.etaLam
#print axioms LeanFX2.Step.eta.etaPath
#print axioms LeanFX2.SmokeEta.demoEtaLam_constructible
#print axioms LeanFX2.SmokeEta.demoEtaPath_constructible

end LeanFX2.SmokeEta
