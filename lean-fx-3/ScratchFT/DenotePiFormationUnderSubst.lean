import FX1Poly.Typed.DenoteKeyedPiFormationFromExistence
import FX1Poly.Core.RawTermSubstConsCommute

/-! Scratch: the denote Π-formation FT arm UNDER A CLOSING SUBSTITUTION (denote #493). Probes (a) whether
`subst σ` distributes over a Π cell by rfl, and (b) the full substitution-aware arm assembled from
`uniformDomainPi_reducibleFromCodomainExistence` + `RawTerm.subst_cons_eq_subst0_lift`. -/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe
open StepStar

-- Probe (a): does subst distribute over the Π cell definitionally?
example {scope targetScope : Nat} (σ : RawTermSubst scope targetScope)
    (domainCode : RawTerm scope) (codomainCode : RawTerm (scope + 1)) :
    RawTerm.subst σ (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil)))
      = .mkGen .gen_piTyCode ()
          (.childCons (RawTerm.subst σ domainCode)
            (.childCons (RawTerm.subst (RawTermSubst.lift σ) codomainCode) .childNil)) := by
  rfl

-- Probe (b): the full substitution-aware Π-formation arm.
theorem piFormationUnderClosingSubstitution {scope targetScope : Nat} (env : Nat → Nat)
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {substitution : RawTermSubst scope targetScope}
    (domainCandidate : RawTerm targetScope → Prop)
    (domainReducible : ∀ level : Nat,
      ReducibleTypeAtDenote env level (RawTerm.subst substitution domainCode) domainCandidate)
    (codomainReducible : ∀ argument : RawTerm targetScope, domainCandidate argument →
      IsReducibleTypeAtAllDenoteLevels env
        (RawTerm.subst (RawTermSubst.cons argument substitution) codomainCode)) :
    IsReducibleTypeAtAllDenoteLevels env
      (RawTerm.subst substitution
        (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil)))) := by
  show IsReducibleTypeAtAllDenoteLevels env
    (.mkGen .gen_piTyCode ()
      (.childCons (RawTerm.subst substitution domainCode)
        (.childCons (RawTerm.subst (RawTermSubst.lift substitution) codomainCode) .childNil)))
  refine uniformDomainPi_reducibleFromCodomainExistence env domainCandidate domainReducible
    (fun argument argumentInDomain => ?_)
  rw [← RawTerm.subst_cons_eq_subst0_lift codomainCode argument substitution]
  exact codomainReducible argument argumentInDomain

end FX1Poly.Typed

#print axioms FX1Poly.Typed.piFormationUnderClosingSubstitution
