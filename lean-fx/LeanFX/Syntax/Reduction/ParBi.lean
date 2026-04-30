import LeanFX.Syntax.Reduction.ParRed

namespace LeanFX.Syntax
open LeanFX.Mode

variable {level : Nat}

/-! ## `Step.par.isBi` — βι-only restriction predicate.

A Prop-valued inductive predicate over `Step.par` proofs that
witnesses "this step does not use η-arrow or η-sigma anywhere".

Why a separate predicate rather than a separate inductive copy of
`Step.par`?  The key invariant is constructor-by-constructor: each
Bi case mirrors a Step.par βι constructor and recursively requires
its sub-proofs to be Bi.  η constructors have no Bi case, so a
typed cd_lemma proven by induction-on-step-with-Bi-hypothesis
discharges the η constructors via vacuous case match (no Bi
constructor matches `Step.par.etaArrow _` or `Step.par.etaSigma _`).

This unblocks `Step.par.cd_lemma_star` for βι-restricted parallel
reductions — the form the task list (#988) explicitly calls for. -/
inductive Step.par.isBi :
    ∀ {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
      {termType : Ty level scope}
      {sourceTerm targetTerm : Term ctx termType},
    Step.par sourceTerm targetTerm → Prop
  /-- Reflexivity is βι. -/
  | refl : ∀ {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
        {termType : Ty level scope} (term : Term ctx termType),
      Step.par.isBi (Step.par.refl term)
  /-- Non-dependent application congruence is βι. -/
  | app : ∀ {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
        {domainType codomainType : Ty level scope}
        {functionTerm functionTerm' :
            Term ctx (Ty.arrow domainType codomainType)}
        {argumentTerm argumentTerm' : Term ctx domainType}
        {functionStep : Step.par functionTerm functionTerm'}
        {argumentStep : Step.par argumentTerm argumentTerm'},
      Step.par.isBi functionStep → Step.par.isBi argumentStep →
      Step.par.isBi (Step.par.app functionStep argumentStep)
  /-- Non-dependent λ-body congruence is βι. -/
  | lam : ∀ {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
        {domainType codomainType : Ty level scope}
        {body body' : Term (ctx.cons domainType) codomainType.weaken}
        {bodyStep : Step.par body body'},
      Step.par.isBi bodyStep →
      Step.par.isBi
        (Step.par.lam (codomainType := codomainType) bodyStep)
  /-- Dependent λ-body congruence is βι. -/
  | lamPi : ∀ {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
        {domainType : Ty level scope}
        {codomainType : Ty level (scope + 1)}
        {body body' : Term (ctx.cons domainType) codomainType}
        {bodyStep : Step.par body body'},
      Step.par.isBi bodyStep →
      Step.par.isBi (Step.par.lamPi (domainType := domainType) bodyStep)
  /-- Dependent application congruence is βι. -/
  | appPi : ∀ {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
        {domainType : Ty level scope}
        {codomainType : Ty level (scope + 1)}
        {functionTerm functionTerm' :
            Term ctx (Ty.piTy domainType codomainType)}
        {argumentTerm argumentTerm' : Term ctx domainType}
        {functionStep : Step.par functionTerm functionTerm'}
        {argumentStep : Step.par argumentTerm argumentTerm'},
      Step.par.isBi functionStep → Step.par.isBi argumentStep →
      Step.par.isBi (Step.par.appPi functionStep argumentStep)
  /-- Σ-pair congruence is βι. -/
  | pair : ∀ {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
        {firstType : Ty level scope}
        {secondType : Ty level (scope + 1)}
        {firstVal firstVal' : Term ctx firstType}
        {secondVal secondVal' : Term ctx (secondType.subst0 firstType)}
        {firstStep : Step.par firstVal firstVal'}
        {secondStep : Step.par secondVal secondVal'},
      Step.par.isBi firstStep → Step.par.isBi secondStep →
      Step.par.isBi (Step.par.pair firstStep secondStep)
  /-- First-projection congruence is βι. -/
  | fst : ∀ {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
        {firstType : Ty level scope}
        {secondType : Ty level (scope + 1)}
        {pairTerm pairTerm' : Term ctx (Ty.sigmaTy firstType secondType)}
        {pairStep : Step.par pairTerm pairTerm'},
      Step.par.isBi pairStep →
      Step.par.isBi (Step.par.fst pairStep)
  /-- Second-projection congruence is βι. -/
  | snd : ∀ {mode : Mode} {level scope : Nat} {ctx : Ctx mode level scope}
        {firstType : Ty level scope}
        {secondType : Ty level (scope + 1)}
        {pairTerm pairTerm' : Term ctx (Ty.sigmaTy firstType secondType)}
        {pairStep : Step.par pairTerm pairTerm'},
      Step.par.isBi pairStep →
      Step.par.isBi (Step.par.snd pairStep)

end LeanFX.Syntax
