import FX1Poly.Typed.DenoteKeyedAbstractionMember
import FX1Poly.Core.RawTermSubstConsCommute

/-! Scratch SN-D3: the FT-shaped (under closing substitution) denote λ member arm.  Mirrors
`piFormationUnderClosingSubstitution`: `subst σ (Π A B) = Π (subst σ A) (subst (lift σ) B)` and
`subst σ (lam body) = lam (subst (lift σ) body)` by rfl (via `show`); the codomain and body premises arrive in
the FT IH shape (under `cons argument σ`), bridged to the `subst0 … (lift σ)` shape `abstractionMemberAtDenote`
wants via `RawTerm.subst_cons_eq_subst0_lift`. -/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe
open StepStar

theorem abstractionMemberUnderClosingSubstitution {scope targetScope : Nat} (env : Nat → Nat) (level : Nat)
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {body : RawTerm (scope + 1)} {substitution : RawTermSubst scope targetScope}
    {domainCandidate : RawTerm targetScope → Prop}
    {codomainCandidate : RawTerm targetScope → (RawTerm targetScope → Prop)}
    (domainReducible :
      ReducibleTypeAtDenote env level (RawTerm.subst substitution domainCode) domainCandidate)
    (codomainReducible : ∀ argument : RawTerm targetScope, domainCandidate argument →
      ReducibleTypeAtDenote env level
        (RawTerm.subst (RawTermSubst.cons argument substitution) codomainCode)
        (codomainCandidate argument))
    (domainArgumentsSN : ∀ argument : RawTerm targetScope, domainCandidate argument →
      IsStronglyNormalizing argument)
    (bodyReducible : ∀ argument : RawTerm targetScope, domainCandidate argument →
      codomainCandidate argument
        (RawTerm.subst (RawTermSubst.cons argument substitution) body)) :
    IsReducibleMemberAtDenote env level
      (RawTerm.subst substitution
        (.mkGen .gen_piTyCode () (.childCons domainCode (.childCons codomainCode .childNil))))
      (RawTerm.subst substitution
        (.mkGen .gen_lam () (.childCons body .childNil))) := by
  show IsReducibleMemberAtDenote env level
    (.mkGen .gen_piTyCode ()
      (.childCons (RawTerm.subst substitution domainCode)
        (.childCons (RawTerm.subst (RawTermSubst.lift substitution) codomainCode) .childNil)))
    (.mkGen .gen_lam ()
      (.childCons (RawTerm.subst (RawTermSubst.lift substitution) body) .childNil))
  refine abstractionMemberAtDenote (codomainCandidate := codomainCandidate) env level domainReducible
    (fun argument argumentInDomain => ?_) domainArgumentsSN
    (fun argument argumentInDomain => ?_)
  · rw [← RawTerm.subst_cons_eq_subst0_lift codomainCode argument substitution]
    exact codomainReducible argument argumentInDomain
  · rw [← RawTerm.subst_cons_eq_subst0_lift body argument substitution]
    exact bodyReducible argument argumentInDomain

end FX1Poly.Typed

#print axioms FX1Poly.Typed.abstractionMemberUnderClosingSubstitution
